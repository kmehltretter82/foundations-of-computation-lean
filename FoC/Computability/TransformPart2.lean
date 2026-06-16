import FoC.Computability.TransformPart1

namespace FoC
namespace Computability
namespace TuringMachine
open Foundation
open Languages
open Classical

theorem normalizedDeciderToAcceptor_sweepRight_target_zero_halts
    (M : TuringMachine symbol state) (zero one : symbol)
    (markedLeft blanksLeft : Nat) (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightTargetTape zero one markedLeft blanksLeft 0 tail } := by
  let acceptConfig :
      Configuration symbol (NormalizedDeciderToAcceptorState state) :=
    { state := NormalizedDeciderToAcceptorState.accept,
      tape := Tape.move Direction.right
        (Tape.write (some one)
          (scannerRightTargetTape zero one markedLeft blanksLeft 0 tail)) }
  have hstep :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepRight,
          tape := scannerRightTargetTape zero one markedLeft blanksLeft 0 tail }
        acceptConfig := by
    exact normalizedDeciderToAcceptor_sweepRight_accept_step
      M zero one (by simp [scannerRightTargetTape, Tape.read])
  exact ⟨acceptConfig,
    Computes.step hstep (Computes.refl acceptConfig), rfl⟩

theorem normalizedDeciderToAcceptor_sweepLeft_target_zero_halts
    (M : TuringMachine symbol state) (zero one : symbol)
    (markedRight blanksRight : Nat) (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftTargetTape zero one markedRight blanksRight 0 tail } := by
  let acceptConfig :
      Configuration symbol (NormalizedDeciderToAcceptorState state) :=
    { state := NormalizedDeciderToAcceptorState.accept,
      tape := Tape.move Direction.right
        (Tape.write (some one)
          (scannerLeftTargetTape zero one markedRight blanksRight 0 tail)) }
  have hstep :
      Step (normalizedDeciderToAcceptor M zero one)
        { state := NormalizedDeciderToAcceptorState.sweepLeft,
          tape := scannerLeftTargetTape zero one markedRight blanksRight 0 tail }
        acceptConfig := by
    exact normalizedDeciderToAcceptor_sweepLeft_accept_step
      M zero one (by simp [scannerLeftTargetTape, Tape.read])
  exact ⟨acceptConfig,
    Computes.step hstep (Computes.refl acceptConfig), rfl⟩

theorem normalizedDeciderToAcceptor_sweepRight_target_halts
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (blanksRight markedLeft blanksLeft : Nat)
    (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepRight,
        tape := scannerRightTargetTape zero one markedLeft blanksLeft
          blanksRight tail } := by
  induction blanksRight generalizing markedLeft blanksLeft with
  | zero =>
      exact normalizedDeciderToAcceptor_sweepRight_target_zero_halts
        M zero one markedLeft blanksLeft tail
  | succ blanksRight ih =>
      exact halts_from_of_computes_prefix
        (normalizedDeciderToAcceptor_sweepRight_target_blank_cycle
          M hzeroOne markedLeft blanksLeft blanksRight tail)
        (ih (markedLeft + 2) blanksLeft.pred)

theorem normalizedDeciderToAcceptor_sweepLeft_target_halts
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one)
    (blanksLeft markedRight blanksRight : Nat)
    (tail : List (Option symbol)) :
    HaltsFrom (normalizedDeciderToAcceptor M zero one)
      { state := NormalizedDeciderToAcceptorState.sweepLeft,
        tape := scannerLeftTargetTape zero one markedRight blanksRight
          blanksLeft tail } := by
  induction blanksLeft generalizing markedRight blanksRight with
  | zero =>
      exact normalizedDeciderToAcceptor_sweepLeft_target_zero_halts
        M zero one markedRight blanksRight tail
  | succ blanksLeft ih =>
      exact halts_from_of_computes_prefix
        (normalizedDeciderToAcceptor_sweepLeft_target_blank_cycle
          M hzeroOne markedRight blanksRight blanksLeft tail)
        (ih (markedRight + 2) blanksRight.pred)

/-!
**Normalized output to scanner starts.**  A halted tape with normalized output
{lit}`[one]` has exactly one nonblank contribution to the output list. The
following list lemmas split such a tape into the head, right-side, and left-side
scanner-start cases used by {lit}`normalizedOutputScannerComplete`.
-/

theorem filterMap_singleton_decompose
    {cells : List (Option symbol)} {one : symbol}
    (h : cells.filterMap (fun cell => cell) = [one]) :
    exists blanks : Nat, exists tail : List (Option symbol),
      cells = scannerBlankBlock blanks ++ some one :: tail := by
  induction cells with
  | nil =>
      simp at h
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp at h
          rcases ih h with ⟨blanks, tail, htail⟩
          exists blanks + 1
          exists tail
          simp [scannerBlankBlock, List.replicate_succ, htail]
      | some a =>
          simp at h
          exists 0
          exists rest
          simp [scannerBlankBlock, h.left]

theorem filterMap_nil_eq_blankBlock
    {cells : List (Option symbol)}
    (h : cells.filterMap (fun cell => cell) = ([] : List symbol)) :
    cells = scannerBlankBlock cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          have hrest :
              rest.filterMap (fun cell => cell) = ([] : List symbol) := by
            simpa using h
          rw [ih hrest]
          simp [scannerBlankBlock, List.replicate_succ]
      | some a =>
          simp at h

theorem filterMap_nil_decompose
    {cells : List (Option symbol)}
    (h : cells.filterMap (fun cell => cell) = ([] : List symbol)) :
    exists blanks : Nat, cells = scannerBlankBlock blanks := by
  exact ⟨cells.length, filterMap_nil_eq_blankBlock h⟩

theorem filterMap_of_reverse_nil
    {cells : List (Option symbol)}
    (h : cells.reverse.filterMap (fun cell => cell) = ([] : List symbol)) :
    cells.filterMap (fun cell => cell) = ([] : List symbol) := by
  have hrev :
      (cells.filterMap (fun cell => cell)).reverse = ([] : List symbol) := by
    simpa [List.filterMap_reverse] using h
  simpa using congrArg List.reverse hrev

theorem filterMap_of_reverse_singleton
    {cells : List (Option symbol)} {one : symbol}
    (h : cells.reverse.filterMap (fun cell => cell) = [one]) :
    cells.filterMap (fun cell => cell) = [one] := by
  have hrev :
      (cells.filterMap (fun cell => cell)).reverse = [one] := by
    simpa [List.filterMap_reverse] using h
  simpa using congrArg List.reverse hrev

def NormalizedOutputScannerComplete
    (M : TuringMachine symbol state) (zero one : symbol) : Prop :=
  forall final : Configuration symbol state,
    Halted M final ->
      Tape.normalizedOutput final.tape = [one] ->
        HaltsFrom (normalizedDeciderToAcceptor M zero one)
          (normalizedRunConfig final)

theorem normalizedOutputScannerComplete
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one) :
    NormalizedOutputScannerComplete M zero one := by
  intro final hhalt hout
  rcases final with ⟨finalState, tape⟩
  cases tape with
  | mk left head right =>
      simp [Halted] at hhalt
      cases head with
      | none =>
          have hsplit :
              (left.reverse.filterMap (fun cell => cell) = ([] : List symbol) ∧
                  right.filterMap (fun cell => cell) = [one]) ∨
                (left.reverse.filterMap (fun cell => cell) = [one] ∧
                  right.filterMap (fun cell => cell) = ([] : List symbol)) := by
            have hfull :
                left.reverse.filterMap (fun cell => cell) ++
                    right.filterMap (fun cell => cell) = [one] := by
              simpa [Tape.normalizedOutput, Tape.cells,
                List.filterMap_append] using hout
            exact List.append_eq_singleton_iff.mp hfull
          cases hsplit with
          | inl hright =>
              rcases hright with ⟨hleftOut, hrightOut⟩
              rcases filterMap_nil_decompose
                  (filterMap_of_reverse_nil hleftOut) with
                ⟨blanksLeftCtx, hleftBlank⟩
              rcases filterMap_singleton_decompose hrightOut with
                ⟨blanksRight, tail, hrightShape⟩
              let startConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                normalizedRunConfig
                  { state := finalState,
                    tape := { left := left, head := none, right := right } }
              let targetConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                { state := NormalizedDeciderToAcceptorState.sweepRight,
                  tape := scannerRightTargetTape zero one 1 blanksLeftCtx
                    blanksRight tail }
              have hstep :
                  Step (normalizedDeciderToAcceptor M zero one)
                    startConfig targetConfig := by
                cases blanksRight with
                | zero =>
                    simpa [startConfig, targetConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftBlank, hrightShape, scannerRightTargetTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
                | succ blanksRight =>
                    simpa [startConfig, targetConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftBlank, hrightShape, scannerRightTargetTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write,
                      List.replicate_succ]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
              exact halts_from_of_computes_prefix
                (computes_of_step hstep)
                (normalizedDeciderToAcceptor_sweepRight_target_halts
                  M hzeroOne blanksRight 1 blanksLeftCtx tail)
          | inr hleft =>
              rcases hleft with ⟨hleftOut, hrightOut⟩
              rcases filterMap_nil_decompose hrightOut with
                ⟨rightBlanks, hrightBlank⟩
              have hleftForward :
                  left.filterMap (fun cell => cell) = [one] :=
                filterMap_of_reverse_singleton hleftOut
              rcases filterMap_singleton_decompose hleftForward with
                ⟨blanksLeft, tail, hleftShape⟩
              let startConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                normalizedRunConfig
                  { state := finalState,
                    tape := { left := left, head := none, right := right } }
              let afterRunConfig :
                  Configuration symbol
                    (NormalizedDeciderToAcceptorState state) :=
                { state := NormalizedDeciderToAcceptorState.sweepRight,
                  tape :=
                    scannerRightCrossTape zero 1
                      (scannerBlankBlock blanksLeft ++ some one :: tail)
                      (scannerBlankBlock rightBlanks) }
              have hstepRun :
                  Step (normalizedDeciderToAcceptor M zero one)
                    startConfig afterRunConfig := by
                cases rightBlanks with
                | zero =>
                    simpa [startConfig, afterRunConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftShape, hrightBlank, scannerRightCrossTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
                | succ rightPred =>
                    simpa [startConfig, afterRunConfig, normalizedRunConfig,
                      normalizedDeciderToAcceptor,
                      normalizedDeciderToAcceptorTransition, hhalt,
                      hleftShape, hrightBlank, scannerRightCrossTape,
                      scannerBlankBlock, scannerZeroBlock, Tape.read,
                      Tape.move, Tape.moveRight, Tape.write,
                      List.replicate_succ]
                      using
                        (Step.mk
                          (M := normalizedDeciderToAcceptor M zero one)
                          (c := startConfig)
                          (write := some zero)
                          (dir := Direction.right)
                          (nextState :=
                            NormalizedDeciderToAcceptorState.sweepRight)
                          (by
                            simp [startConfig, normalizedRunConfig,
                              normalizedDeciderToAcceptor,
                              normalizedDeciderToAcceptorTransition, hhalt,
                              Tape.read]))
              let rightCtx :=
                some zero :: scannerBlankBlock rightBlanks.pred
              let leftRest :=
                scannerZeroBlock zero 1 ++
                  scannerBlankBlock blanksLeft ++ some one :: tail
              let afterRightMark : Tape symbol :=
                scannerLeftCrossTape zero 0 rightCtx leftRest
              have hstepRight :
                  Step (normalizedDeciderToAcceptor M zero one)
                    afterRunConfig
                    { state := NormalizedDeciderToAcceptorState.sweepLeft,
                      tape := afterRightMark } := by
                cases rightBlanks with
                | zero =>
                    simpa [afterRunConfig, afterRightMark, rightCtx,
                      leftRest, scannerRightCrossTape,
                      scannerLeftCrossTape, scannerBlankBlock,
                      scannerZeroBlock, Tape.read, Tape.move,
                      Tape.moveLeft, Tape.write]
                      using
                        normalizedDeciderToAcceptor_sweepRight_blank_step
                          M zero one
                          (T := afterRunConfig.tape)
                          (by
                            simp [afterRunConfig, scannerRightCrossTape,
                              Tape.read, scannerBlankBlock])
                | succ rightPred =>
                    simpa [afterRunConfig, afterRightMark, rightCtx,
                      leftRest, scannerRightCrossTape,
                      scannerLeftCrossTape, scannerBlankBlock,
                      scannerZeroBlock, Tape.read, Tape.move,
                      Tape.moveLeft, Tape.write, List.replicate_succ]
                      using
                        normalizedDeciderToAcceptor_sweepRight_blank_step
                          M zero one
                          (T := afterRunConfig.tape)
                          (by
                            simp [afterRunConfig, scannerRightCrossTape,
                              Tape.read, scannerBlankBlock,
                              List.replicate_succ])
              have hcrossLeft :
                  Computes (normalizedDeciderToAcceptor M zero one)
                    { state := NormalizedDeciderToAcceptorState.sweepLeft,
                      tape := afterRightMark }
                    { state := NormalizedDeciderToAcceptorState.sweepLeft,
                      tape := scannerLeftTargetTape zero one 2
                        rightBlanks.pred blanksLeft tail } := by
                have h :=
                  normalizedDeciderToAcceptor_sweepLeft_cross_zeroBlock
                    M hzeroOne 1 0 rightCtx
                    (scannerBlankBlock blanksLeft ++ some one :: tail)
                cases blanksLeft with
                | zero =>
                    simpa [afterRightMark, rightCtx, leftRest,
                      scannerLeftTargetTape, scannerLeftCrossTape,
                      scannerBlankBlock, scannerZeroBlock,
                      List.replicate_succ, List.append_assoc]
                      using h
                | succ blanksLeft =>
                    simpa [afterRightMark, rightCtx, leftRest,
                      scannerLeftTargetTape, scannerLeftCrossTape,
                      scannerBlankBlock, scannerZeroBlock,
                      List.replicate_succ, List.append_assoc]
                      using h
              exact halts_from_of_computes_prefix
                (Computes.step hstepRun
                  (Computes.step hstepRight hcrossLeft))
                (normalizedDeciderToAcceptor_sweepLeft_target_halts
                  M hzeroOne blanksLeft 2 rightBlanks.pred tail)
      | some a =>
          by_cases ha : a = one
          · subst a
            let startConfig :
                Configuration symbol
                  (NormalizedDeciderToAcceptorState state) :=
              normalizedRunConfig
                { state := finalState,
                  tape := { left := left, head := some one, right := right } }
            let acceptConfig :
                Configuration symbol
                  (NormalizedDeciderToAcceptorState state) :=
              { state := NormalizedDeciderToAcceptorState.accept,
                tape := Tape.move Direction.right
                  (Tape.write (some one)
                    { left := left, head := some one, right := right }) }
            have hstep :
                Step (normalizedDeciderToAcceptor M zero one)
                  startConfig acceptConfig := by
              simpa [startConfig, acceptConfig, normalizedRunConfig,
                normalizedDeciderToAcceptor,
                normalizedDeciderToAcceptorTransition, hhalt, Tape.read]
                using
                  (Step.mk
                    (M := normalizedDeciderToAcceptor M zero one)
                    (c := startConfig)
                    (write := some one)
                    (dir := Direction.right)
                    (nextState := NormalizedDeciderToAcceptorState.accept)
                    (by
                      simp [startConfig, normalizedRunConfig,
                        normalizedDeciderToAcceptor,
                        normalizedDeciderToAcceptorTransition, hhalt,
                        Tape.read]))
            exact ⟨acceptConfig,
              Computes.step hstep (Computes.refl acceptConfig), rfl⟩
          · have haMem :
                a ∈ (left.reverse ++ some a :: right).filterMap
                    (fun cell => cell) := by
              simp
            have houtCells :
                (left.reverse ++ some a :: right).filterMap
                    (fun cell => cell) = [one] := by
              simpa [Tape.normalizedOutput, Tape.cells] using hout
            rw [houtCells] at haMem
            simp at haMem
            exact False.elim (ha haMem)

theorem normalizedDeciderToAcceptor_halts_of_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    HaltsOnInput (normalizedDeciderToAcceptor M zero one)
      (EncodeWord encodeInput w) := by
  rcases (hdec w).left hw with ⟨final, hcomp, hhalt, hout⟩
  have hsim := normalizedDeciderToAcceptor_simulates_computes
    (M := M) (zero := zero) (one := one) hstop hcomp
  exact halts_from_of_computes_prefix hsim
    (normalizedOutputScannerComplete M hzeroOne final hhalt hout)

theorem normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    AcceptsLanguage (normalizedDeciderToAcceptor M zero one) encodeInput L := by
  intro w
  constructor
  · exact normalizedDeciderToAcceptor_halts_sound_of_stopped_decider
      h.left h.right.left h.right.right
  · exact normalizedDeciderToAcceptor_halts_of_mem
      h.left h.right.left h.right.right

theorem stoppedDecidesLanguage_to_turingAcceptable
    {symbol state input : Type}
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    TuringAcceptable L := by
  exists symbol
  exists NormalizedDeciderToAcceptorState state
  exists normalizedDeciderToAcceptor M zero one
  exists encodeInput
  exact normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider h

theorem stoppedTuringDecidable_to_turingAcceptable
    {input : Type} {L : Language input}
    (h : StoppedTuringDecidable L) :
    TuringAcceptable L := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exists symbol
  exists NormalizedDeciderToAcceptorState state
  exists normalizedDeciderToAcceptor M zero one
  exists encodeInput
  exact normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider hdec

def runConfig (c : Configuration symbol state) :
    Configuration symbol (DeciderToAcceptorState state) where
  state := DeciderToAcceptorState.run c.state
  tape := c.tape

noncomputable def deciderToAcceptorTransition
    (M : TuringMachine symbol state) (one : symbol) :
    DeciderToAcceptorState state -> Option symbol ->
      Option (Option symbol × Direction × DeciderToAcceptorState state)
  | DeciderToAcceptorState.run s, cell =>
      if s = M.halt then
        if cell = some one then
          some (cell, Direction.right, DeciderToAcceptorState.accept)
        else
          some (cell, Direction.right, DeciderToAcceptorState.loop)
      else
        match M.transition s cell with
        | some (write, dir, nextState) =>
            some (write, dir, DeciderToAcceptorState.run nextState)
        | none => none
  | DeciderToAcceptorState.accept, _ => none
  | DeciderToAcceptorState.loop, cell =>
      some (cell, Direction.right, DeciderToAcceptorState.loop)

noncomputable def deciderToAcceptor
    (M : TuringMachine symbol state) (one : symbol) :
    TuringMachine symbol (DeciderToAcceptorState state) where
  start := DeciderToAcceptorState.run M.start
  halt := DeciderToAcceptorState.accept
  transition := deciderToAcceptorTransition M one
  statesFinite := DeciderToAcceptorState.finite M.statesFinite

@[simp] theorem deciderToAcceptor_initial
    (M : TuringMachine symbol state) (one : symbol) (w : Word symbol) :
    (deciderToAcceptor M one).initial w =
      runConfig (M.initial w) :=
  rfl

theorem deciderToAcceptor_step_run
    {M : TuringMachine symbol state} {one : symbol}
    {c d : Configuration symbol state}
    (hnot : c.state ≠ M.halt)
    (hstep : Step M c d) :
    Step (deciderToAcceptor M one) (runConfig c) (runConfig d) := by
  cases hstep with
  | mk haction =>
      exact Step.mk (by
        simp [runConfig, deciderToAcceptor, deciderToAcceptorTransition,
          hnot, haction])

theorem deciderToAcceptor_step_run_of_stopped
    {M : TuringMachine symbol state} {one : symbol}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hstep : Step M c d) :
    Step (deciderToAcceptor M one) (runConfig c) (runConfig d) := by
  have hnot : c.state ≠ M.halt := by
    intro hhalt
    exact False.elim (no_step_from_halted hstop hhalt hstep)
  exact deciderToAcceptor_step_run hnot hstep

theorem deciderToAcceptor_simulates_computes
    {M : TuringMachine symbol state} {one : symbol}
    (hstop : HaltingTransitionsDisabled M)
    {c d : Configuration symbol state}
    (hcomp : Computes M c d) :
    Computes (deciderToAcceptor M one) (runConfig c) (runConfig d) := by
  induction hcomp with
  | refl c =>
      exact Computes.refl (runConfig c)
  | step hstep _ ih =>
      exact Computes.step (deciderToAcceptor_step_run_of_stopped hstop hstep) ih

def DeciderToAcceptorInvariant
    (M : TuringMachine symbol state) (one : symbol) (input : Word symbol)
    (c : Configuration symbol (DeciderToAcceptorState state)) : Prop :=
  match c.state with
  | DeciderToAcceptorState.run s =>
      Computes M (M.initial input) { state := s, tape := c.tape }
  | DeciderToAcceptorState.accept =>
      exists halted : Configuration symbol state,
        Computes M (M.initial input) halted ∧
          Halted M halted ∧ Tape.read halted.tape = some one
  | DeciderToAcceptorState.loop => True

theorem deciderToAcceptor_invariant_step
    {M : TuringMachine symbol state} {one : symbol} {input : Word symbol}
    {c d : Configuration symbol (DeciderToAcceptorState state)}
    (hinv : DeciderToAcceptorInvariant M one input c)
    (hstep : Step (deciderToAcceptor M one) c d) :
    DeciderToAcceptorInvariant M one input d := by
  cases hstep with
  | mk haction =>
      cases hcstate : c.state with
      | run s =>
          simp [DeciderToAcceptorInvariant, hcstate] at hinv
          by_cases hhalt : s = M.halt
          · by_cases hone : Tape.read c.tape = some one
            · simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                hhalt, hone] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              cases hwrite
              cases hdir
              cases hnext
              simp [DeciderToAcceptorInvariant]
              exact ⟨{ state := s, tape := c.tape }, hinv, hhalt, hone⟩
            · simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                hhalt, hone] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              cases hwrite
              cases hdir
              cases hnext
              simp [DeciderToAcceptorInvariant]
          · cases hM : M.transition s (Tape.read c.tape) with
            | none =>
                simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                  hhalt, hM] at haction
            | some action =>
                rcases action with ⟨write, dir, nextState⟩
                simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate,
                  hhalt, hM] at haction
                rcases haction with ⟨hwrite, hdir, hnext⟩
                cases hwrite
                cases hdir
                cases hnext
                simp [DeciderToAcceptorInvariant]
                exact computes_trans hinv
                  (Computes.step (Step.mk hM) (Computes.refl _))
      | accept =>
          simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate] at haction
      | loop =>
          simp [deciderToAcceptor, deciderToAcceptorTransition, hcstate] at haction
          rcases haction with ⟨hwrite, hdir, hnext⟩
          cases hwrite
          cases hdir
          cases hnext
          simp [DeciderToAcceptorInvariant]

theorem deciderToAcceptor_invariant_of_computesIn
    {M : TuringMachine symbol state} {one : symbol} {input : Word symbol}
    {n : Nat}
    {c d : Configuration symbol (DeciderToAcceptorState state)}
    (hcomp : ComputesIn (deciderToAcceptor M one) n c d)
    (hinv : DeciderToAcceptorInvariant M one input c) :
    DeciderToAcceptorInvariant M one input d := by
  induction hcomp with
  | zero c =>
      exact hinv
  | succ hstep _ ih =>
      exact ih (deciderToAcceptor_invariant_step hinv hstep)

theorem deciderToAcceptor_initial_invariant
    (M : TuringMachine symbol state) (one : symbol) (input : Word symbol) :
    DeciderToAcceptorInvariant M one input
      ((deciderToAcceptor M one).initial input) := by
  simp [deciderToAcceptor_initial, DeciderToAcceptorInvariant, runConfig]
  exact Computes.refl (M.initial input)

theorem deciderToAcceptor_halts_of_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hdec : DecidesLanguageByHeadOutput M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    HaltsOnInput (deciderToAcceptor M one) (EncodeWord encodeInput w) := by
  rcases (hdec w).left hw with ⟨final, hcomp, hhalt, hread⟩
  have hsim := deciderToAcceptor_simulates_computes
    (M := M) (one := one) hstop hcomp
  have hhaltState : final.state = M.halt := hhalt
  let acceptConfig :
      Configuration symbol (DeciderToAcceptorState state) :=
    { state := DeciderToAcceptorState.accept,
      tape := Tape.move Direction.right (Tape.write (some one) final.tape) }
  have hstep :
      Step (deciderToAcceptor M one) (runConfig final) acceptConfig := by
    exact Step.mk (by
      simp [runConfig, deciderToAcceptor,
        deciderToAcceptorTransition, hhaltState, hread])
  exact ⟨acceptConfig,
    computes_trans hsim (Computes.step hstep (Computes.refl acceptConfig)),
    rfl⟩

theorem deciderToAcceptor_halts_sound_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguageByHeadOutput M encodeInput zero one L)
    {w : Word input}
    (hhalt :
      HaltsOnInput (deciderToAcceptor M one) (EncodeWord encodeInput w)) :
    w ∈ L := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases computes_to_computesIn hcomp with ⟨n, hcompIn⟩
  have hinv :=
    deciderToAcceptor_invariant_of_computesIn
      (M := M) (one := one) (input := EncodeWord encodeInput w)
      hcompIn
      (deciderToAcceptor_initial_invariant
        M one (EncodeWord encodeInput w))
  cases hstate : final.state with
  | run s =>
      simp [Halted, deciderToAcceptor, hstate] at hfinal
  | accept =>
      simp [DeciderToAcceptorInvariant, hstate] at hinv
      rcases hinv with ⟨halted, hcompM, hhalted, hreadOne⟩
      apply Classical.byContradiction
      intro hnot
      rcases (hdec w).right hnot with ⟨rejectFinal, hcompReject,
        hhaltReject, hreadReject⟩
      have hEq :=
        computes_to_halted_unique hstop hcompM hhalted
          hcompReject hhaltReject
      have hreadZero : Tape.read halted.tape = some zero := by
        rw [hEq]
        exact hreadReject
      rw [hreadOne] at hreadZero
      have honeZero : one = zero := by
        simpa using hreadZero
      exact hzeroOne honeZero.symm
  | loop =>
      simp [Halted, deciderToAcceptor, hstate] at hfinal

theorem deciderToAcceptor_acceptsLanguage_of_stopped_decider
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (hdec : DecidesLanguageByHeadOutput M encodeInput zero one L) :
    AcceptsLanguage (deciderToAcceptor M one) encodeInput L := by
  intro w
  constructor
  · exact deciderToAcceptor_halts_sound_of_stopped_decider
      hstop hzeroOne hdec
  · exact deciderToAcceptor_halts_of_mem hstop hdec

theorem stoppedDecidesLanguageByHeadOutput_to_turingAcceptable
    {symbol state input : Type}
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguageByHeadOutput M encodeInput zero one L) :
    TuringAcceptable L := by
  exists symbol
  exists DeciderToAcceptorState state
  exists deciderToAcceptor M one
  exists encodeInput
  exact deciderToAcceptor_acceptsLanguage_of_stopped_decider
    h.left h.right.left h.right.right

theorem stoppedTuringDecidableByHeadOutput_to_turingAcceptable
    {input : Type} {L : Language input}
    (h : StoppedTuringDecidableByHeadOutput L) :
    TuringAcceptable L := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exists symbol
  exists DeciderToAcceptorState state
  exists deciderToAcceptor M one
  exists encodeInput
  exact deciderToAcceptor_acceptsLanguage_of_stopped_decider
    hdec.left hdec.right.left hdec.right.right

end TuringMachine

end Computability
end FoC

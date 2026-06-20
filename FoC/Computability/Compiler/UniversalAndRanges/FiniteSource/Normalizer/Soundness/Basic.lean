import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def codePrefixParserNormalizerStateOfParser :
    TransitionListParserState -> CodePrefixParserNormalizerState
  | TransitionListParserState.findCount marker =>
      CodePrefixParserNormalizerState.findCount marker
  | TransitionListParserState.seekCountDone marker =>
      CodePrefixParserNormalizerState.seekCountDone marker
  | TransitionListParserState.seekMarker saved =>
      CodePrefixParserNormalizerState.seekMarker saved
  | TransitionListParserState.enterMarkedPosition =>
      CodePrefixParserNormalizerState.enterMarkedPosition
  | TransitionListParserState.needTransition =>
      CodePrefixParserNormalizerState.needTransition
  | TransitionListParserState.sourceNat =>
      CodePrefixParserNormalizerState.sourceNat
  | TransitionListParserState.readCell =>
      CodePrefixParserNormalizerState.readCell
  | TransitionListParserState.writeCell =>
      CodePrefixParserNormalizerState.writeCell
  | TransitionListParserState.moveField =>
      CodePrefixParserNormalizerState.moveField
  | TransitionListParserState.targetNat =>
      CodePrefixParserNormalizerState.targetNat
  | TransitionListParserState.markPosition =>
      CodePrefixParserNormalizerState.markPosition
  | TransitionListParserState.returnLeft saved =>
      CodePrefixParserNormalizerState.returnLeft saved
  | TransitionListParserState.halt =>
      CodePrefixParserNormalizerState.halt

theorem transitionListParserOptionTape_normalizedOutput
    (leftRev rest : List (Option MachineCodeSymbol)) :
    Tape.normalizedOutput
        (transitionListParserOptionTape leftRev rest) =
      List.append (leftRev.reverse.filterMap (fun cell => cell))
        (rest.filterMap (fun cell => cell)) := by
  cases rest <;>
    simp [Tape.normalizedOutput, Tape.cells,
      transitionListParserOptionTape, List.filterMap_append]

theorem codePrefixParserNormalizer_replicate_append_singleton_tick
    (n : Nat) :
    List.append
        (List.replicate n (some MachineCodeSymbol.tick))
        [some MachineCodeSymbol.tick] =
      List.replicate (n + 1) (some MachineCodeSymbol.tick) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        some MachineCodeSymbol.tick ::
            List.append
              (List.replicate n (some MachineCodeSymbol.tick))
              [some MachineCodeSymbol.tick] =
          some MachineCodeSymbol.tick ::
            List.replicate (n + 1) (some MachineCodeSymbol.tick)
      rw [ih]

theorem codePrefixParserNormalizer_encodeNat_eq_replicate_tick_done
    (n : Nat) :
    MachineDescription.encodeNat n =
      List.append (List.replicate n MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [MachineDescription.encodeNat, ih, List.replicate_succ]

theorem codePrefixParserNormalizer_filterMap_comp_some
    (w : Word MachineCodeSymbol) :
    List.filterMap ((fun cell : Option MachineCodeSymbol => cell) ∘ some)
        w = w := by
  induction w with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [Function.comp, ih]

theorem codePrefixParserNormalizerMarkedNatReverse_eq
    (n : Nat) :
    codePrefixParserNormalizerMarkedNatReverse n =
      none ::
        List.replicate n (some MachineCodeSymbol.tick) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        codePrefixParserNormalizerMarkedNatReverse (n + 1)
            =
          List.append
            (codePrefixParserNormalizerMarkedNatReverse n)
            [some MachineCodeSymbol.tick] := by
              rfl
        _ =
          List.append
            (none ::
              List.replicate n (some MachineCodeSymbol.tick))
            [some MachineCodeSymbol.tick] := by
              rw [ih]
        _ =
          none ::
            List.append
              (List.replicate n (some MachineCodeSymbol.tick))
              [some MachineCodeSymbol.tick] := by
              rfl
        _ =
          none ::
            List.replicate (n + 1)
              (some MachineCodeSymbol.tick) := by
              rw [codePrefixParserNormalizer_replicate_append_singleton_tick]

theorem codePrefixParserNormalizerMachine_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled
      codePrefixParserNormalizerMachine := by
  intro cell
  cases cell <;>
    simp [codePrefixParserNormalizerMachine]

theorem codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
    {c d : TuringMachine.Configuration MachineCodeSymbol
      CodePrefixParserNormalizerState}
    (hprefix :
      TuringMachine.Computes codePrefixParserNormalizerMachine c d)
    (hhalt :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine c) :
    TuringMachine.HaltsFrom codePrefixParserNormalizerMachine d := by
  rcases hhalt with ⟨final, hfinalComp, hfinalHalt⟩
  induction hprefix generalizing final with
  | refl c =>
      exact ⟨final, hfinalComp, hfinalHalt⟩
  | step hstep hrest ih =>
      cases hfinalComp with
      | refl =>
          exact
            False.elim
              (TuringMachine.no_step_from_halted
                codePrefixParserNormalizerMachine_haltingTransitionsDisabled
                hfinalHalt hstep)
      | step hstep' hfinalTail =>
          have hnext :=
            TuringMachine.step_deterministic hstep hstep'
          cases hnext
          exact ih final hfinalTail hfinalHalt

theorem codePrefixParserNormalizerMachine_step_findInitialCount_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_write_right
    (state := CodePrefixParserNormalizerState.findInitialCount)
    (next :=
      CodePrefixParserNormalizerState.seekCountDone
        TransitionListParserMarker.initial)
    (leftRev := leftRev)
    (suffix := suffix)
    (cell := some MachineCodeSymbol.tick)
    (write := some MachineCodeSymbol.blank)
    (by
      simp [codePrefixParserNormalizerMachine])

theorem codePrefixParserNormalizerMachine_step_findInitialCount_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreLeft
        tape :=
          transitionListParserOptionTape leftRev.tail
            (leftRev.head?.join ::
              some MachineCodeSymbol.done :: suffix) } := by
  cases leftRev with
  | nil =>
      simpa using
        codePrefixParserNormalizerMachine_step_keep_left_boundary
          (state := CodePrefixParserNormalizerState.findInitialCount)
          (next := CodePrefixParserNormalizerState.restoreLeft)
          (suffix := suffix)
          (cell := some MachineCodeSymbol.done)
          (by
            simp [codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerKeep])
  | cons leftHead leftTail =>
      simpa using
        codePrefixParserNormalizerMachine_step_keep_left_nonempty
          (state := CodePrefixParserNormalizerState.findInitialCount)
          (next := CodePrefixParserNormalizerState.restoreLeft)
          (leftTail := leftTail)
          (suffix := suffix)
          (leftHead := leftHead)
          (cell := some MachineCodeSymbol.done)
          (by
            simp [codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_findCount_initial_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreLeft
        tape :=
          transitionListParserOptionTape leftRev.tail
            (leftRev.head?.join ::
              some MachineCodeSymbol.done :: suffix) } := by
  cases leftRev with
  | nil =>
      simpa using
        codePrefixParserNormalizerMachine_step_keep_left_boundary
          (state :=
            CodePrefixParserNormalizerState.findCount
              TransitionListParserMarker.initial)
          (next := CodePrefixParserNormalizerState.restoreLeft)
          (suffix := suffix)
          (cell := some MachineCodeSymbol.done)
          (by
            simp [codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerKeep])
  | cons leftHead leftTail =>
      simpa using
        codePrefixParserNormalizerMachine_step_keep_left_nonempty
          (state :=
            CodePrefixParserNormalizerState.findCount
              TransitionListParserMarker.initial)
          (next := CodePrefixParserNormalizerState.restoreLeft)
          (leftTail := leftTail)
          (suffix := suffix)
          (leftHead := leftHead)
          (cell := some MachineCodeSymbol.done)
          (by
            simp [codePrefixParserNormalizerMachine,
              codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_findCount_blank
    (marker : TransitionListParserMarker)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findCount marker
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.blank :: suffix) }
      { state := CodePrefixParserNormalizerState.findCount marker
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.blank :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by
      cases marker <;>
        simp [codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_findCount_saved_done
    (saved : Option MachineCodeSymbol)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_restoreLeft_blank
    (leftHead : Option MachineCodeSymbol)
    (leftTail suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreLeft
        tape :=
          transitionListParserOptionTape
            (leftHead :: leftTail)
            (some MachineCodeSymbol.blank :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreLeft
        tape := transitionListParserOptionTape leftTail
          (leftHead ::
            some MachineCodeSymbol.tick :: suffix) } :=
  codePrefixParserNormalizerMachine_step_write_left_nonempty
    (state := CodePrefixParserNormalizerState.restoreLeft)
    (next := CodePrefixParserNormalizerState.restoreLeft)
    (leftTail := leftTail)
    (suffix := suffix)
    (leftHead := leftHead)
    (cell := some MachineCodeSymbol.blank)
    (write := some MachineCodeSymbol.tick)
    (by
      simp [codePrefixParserNormalizerMachine,
        codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_restoreLeft_none
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreLeft
        tape :=
          transitionListParserOptionTape leftRev
            (none :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreForward
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_write_right
    (state := CodePrefixParserNormalizerState.restoreLeft)
    (next := CodePrefixParserNormalizerState.restoreForward)
    (leftRev := leftRev)
    (suffix := suffix)
    (cell := none)
    (write := some MachineCodeSymbol.done)
    (by
      simp [codePrefixParserNormalizerMachine])

theorem codePrefixParserNormalizer_replicate_tick_append_tick
    (n : Nat) (tail : List (Option MachineCodeSymbol)) :
    List.append (List.replicate n (some MachineCodeSymbol.tick))
        (some MachineCodeSymbol.tick :: tail) =
      List.append (List.replicate (n + 1) (some MachineCodeSymbol.tick))
        tail := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate] using ih

theorem codePrefixParserNormalizer_replicate_append_self
    {α : Type} (cell : α) (n : Nat) (tail : List α) :
    List.append (List.replicate n cell) (cell :: tail) =
      List.append (List.replicate (n + 1) cell) tail := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate] using ih

theorem codePrefixParserNormalizerMachine_computes_findCount_done_restoreForward
    (blanks : Nat)
    (prefixLeft suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (none :: prefixLeft))
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreForward
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: prefixLeft)
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.tick))
              (some MachineCodeSymbol.done :: suffix)) } := by
  induction blanks generalizing suffix with
  | zero =>
      exact
        TuringMachine.Computes.step
          (by
            simpa using
              codePrefixParserNormalizerMachine_step_findCount_initial_done
                (none :: prefixLeft) suffix)
          (by
            simpa using
              TuringMachine.Computes.step
                (codePrefixParserNormalizerMachine_step_restoreLeft_none
                  prefixLeft (some MachineCodeSymbol.done :: suffix))
                (TuringMachine.Computes.refl _))
  | succ blanks ih =>
      have hrestore :
          (tail : List (Option MachineCodeSymbol)) ->
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.restoreLeft
              tape :=
                transitionListParserOptionTape
                  (List.append
                    (List.replicate blanks
                      (some MachineCodeSymbol.blank))
                    (none :: prefixLeft))
                  (some MachineCodeSymbol.blank :: tail) }
            { state := CodePrefixParserNormalizerState.restoreForward
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.done :: prefixLeft)
                  (List.append
                    (List.replicate (blanks + 1)
                      (some MachineCodeSymbol.tick))
                    tail) } := by
        intro tail
        clear ih
        induction blanks generalizing tail with
        | zero =>
            exact
              TuringMachine.Computes.step
                (by
                  simpa using
                    codePrefixParserNormalizerMachine_step_restoreLeft_blank
                      none
                      prefixLeft
                      tail)
                (by
                  simpa using
                    TuringMachine.Computes.step
                      (codePrefixParserNormalizerMachine_step_restoreLeft_none
                        prefixLeft
                        (some MachineCodeSymbol.tick :: tail))
                      (TuringMachine.Computes.refl _))
        | succ blanks ih =>
            exact
              TuringMachine.Computes.step
                (by
                  simpa [List.append_assoc] using
                    codePrefixParserNormalizerMachine_step_restoreLeft_blank
                      (some MachineCodeSymbol.blank)
                      (List.append
                        (List.replicate blanks
                          (some MachineCodeSymbol.blank))
                        (none :: prefixLeft))
                      tail)
                (by
                  rw [←
                    codePrefixParserNormalizer_replicate_tick_append_tick
                      (blanks + 1) tail]
                  exact ih (some MachineCodeSymbol.tick :: tail))
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.append_assoc] using
              codePrefixParserNormalizerMachine_step_findCount_initial_done
                (List.append
                  (List.replicate (blanks + 1)
                    (some MachineCodeSymbol.blank))
                  (none :: prefixLeft))
                suffix)
          (by
            simpa [List.append_assoc] using
              hrestore (some MachineCodeSymbol.done :: suffix))

theorem codePrefixParserNormalizerMachine_computes_findCount_saved_blanks_done
    (saved : Option MachineCodeSymbol)
    (blanks : Nat)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.findCount
            (TransitionListParserMarker.saved saved)
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate blanks (some MachineCodeSymbol.blank))
              (some MachineCodeSymbol.done :: suffix)) }
      { state := CodePrefixParserNormalizerState.restoreSeekMarker saved
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                leftRev)
            suffix } := by
  induction blanks generalizing leftRev with
  | zero =>
      simpa using
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_findCount_saved_done
            saved leftRev suffix)
          (TuringMachine.Computes.refl _)
  | succ blanks ih =>
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.append_assoc] using
              codePrefixParserNormalizerMachine_step_findCount_blank
                (TransitionListParserMarker.saved saved)
                leftRev
                (List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.done :: suffix)))
          (by
            rw [←
              codePrefixParserNormalizer_replicate_append_self
                (some MachineCodeSymbol.blank) blanks leftRev]
            exact ih (some MachineCodeSymbol.blank :: leftRev))

theorem codePrefixParserNormalizerMachine_step_restoreForward_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreForward
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state := CodePrefixParserNormalizerState.restoreForward
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (state := CodePrefixParserNormalizerState.restoreForward)
    (next := CodePrefixParserNormalizerState.restoreForward)
    (leftRev := leftRev)
    (suffix := suffix)
    (cell := some MachineCodeSymbol.tick)
    (by
      simp [codePrefixParserNormalizerMachine,
        codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_restoreForward_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreForward
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (state := CodePrefixParserNormalizerState.restoreForward)
    (next := CodePrefixParserNormalizerState.halt)
    (leftRev := leftRev)
    (suffix := suffix)
    (cell := some MachineCodeSymbol.done)
    (by
      simp [codePrefixParserNormalizerMachine,
        codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_computes_findInitialCount_zero_halt
    (prefixLeft suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape
            (none :: prefixLeft)
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              some MachineCodeSymbol.done :: prefixLeft)
            suffix } :=
  TuringMachine.Computes.step
    (by
      simpa using
        codePrefixParserNormalizerMachine_step_findInitialCount_done
          (none :: prefixLeft) suffix)
    (TuringMachine.Computes.step
      (codePrefixParserNormalizerMachine_step_restoreLeft_none
        prefixLeft (some MachineCodeSymbol.done :: suffix))
      (TuringMachine.Computes.step
        (codePrefixParserNormalizerMachine_step_restoreForward_done
          (some MachineCodeSymbol.done :: prefixLeft) suffix)
        (TuringMachine.Computes.refl _)))

theorem codePrefixParserNormalizerMachine_step_seekCountDone_initial_tick
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.tick :: suffix) }
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.tick :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_step_seekCountDone_initial_done
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Step codePrefixParserNormalizerMachine
      { state :=
          CodePrefixParserNormalizerState.seekCountDone
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape leftRev
            (some MachineCodeSymbol.done :: suffix) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done :: leftRev) suffix } :=
  codePrefixParserNormalizerMachine_step_keep_right
    (by simp [codePrefixParserNormalizerMachine,
      codePrefixParserNormalizerKeep])

theorem codePrefixParserNormalizerMachine_computes_findInitialCount_succ
    (count : Nat)
    (leftRev : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.findInitialCount
        tape :=
          transitionListParserOptionTape leftRev
            ((MachineDescription.encodeNatAppend (Nat.succ count)
              suffix).map some) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (List.append
              ((MachineDescription.encodeNat count).reverse.map some)
              (some MachineCodeSymbol.blank :: leftRev))
            (suffix.map some) } := by
  have htail :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state :=
            CodePrefixParserNormalizerState.seekCountDone
              TransitionListParserMarker.initial
          tape :=
            transitionListParserOptionTape
              (some MachineCodeSymbol.blank :: leftRev)
              ((MachineDescription.encodeNatAppend count suffix).map
                some) }
        { state := CodePrefixParserNormalizerState.needTransition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((MachineDescription.encodeNat count).reverse.map some)
                (some MachineCodeSymbol.blank :: leftRev))
              (suffix.map some) } :=
    codePrefixParserNormalizerMachine_computes_nat_option
      codePrefixParserNormalizerMachine_step_seekCountDone_initial_tick
      codePrefixParserNormalizerMachine_step_seekCountDone_initial_done
      (some MachineCodeSymbol.blank :: leftRev) count suffix
  have hstep :=
    codePrefixParserNormalizerMachine_step_findInitialCount_tick
      leftRev ((MachineDescription.encodeNatAppend count suffix).map some)
  have hcomp :
      TuringMachine.Computes codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.findInitialCount
          tape :=
            transitionListParserOptionTape leftRev
              (some MachineCodeSymbol.tick ::
                (MachineDescription.encodeNatAppend count suffix).map
                  some) }
        { state := CodePrefixParserNormalizerState.needTransition
          tape :=
            transitionListParserOptionTape
              (List.append
                ((MachineDescription.encodeNat count).reverse.map some)
                (some MachineCodeSymbol.blank :: leftRev))
              (suffix.map some) } :=
    TuringMachine.Computes.step hstep htail
  simpa [MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat] using hcomp

def codePrefixParserNormalizerRestoredTicksLeft :
    Nat -> List (Option MachineCodeSymbol) ->
      List (Option MachineCodeSymbol)
  | 0, leftRev => leftRev
  | n + 1, leftRev =>
      codePrefixParserNormalizerRestoredTicksLeft n
        (some MachineCodeSymbol.tick :: leftRev)

theorem codePrefixParserNormalizerMachine_computes_restoreForward_ticks
    (ticks : Nat)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.restoreForward
        tape :=
          transitionListParserOptionTape leftRev
            (List.append
              (List.replicate ticks (some MachineCodeSymbol.tick))
              (some MachineCodeSymbol.done :: suffix)) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              codePrefixParserNormalizerRestoredTicksLeft ticks
                leftRev)
            suffix } := by
  induction ticks generalizing leftRev with
  | zero =>
      simpa using
        TuringMachine.Computes.step
          (codePrefixParserNormalizerMachine_step_restoreForward_done
            leftRev suffix)
          (TuringMachine.Computes.refl _)
  | succ ticks ih =>
      exact
        TuringMachine.Computes.step
          (by
            simpa [List.append_assoc] using
              codePrefixParserNormalizerMachine_step_restoreForward_tick
                leftRev
                (List.append
                  (List.replicate ticks
                    (some MachineCodeSymbol.tick))
                  (some MachineCodeSymbol.done :: suffix)))
          (by
            simpa [codePrefixParserNormalizerRestoredTicksLeft] using
              ih (some MachineCodeSymbol.tick :: leftRev))

theorem codePrefixParserNormalizerMachine_haltsFromIn_needHeader_head
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.needHeader
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists suffix : Word MachineCodeSymbol,
      rest = MachineCodeSymbol.header :: suffix := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  exact ⟨suffix, rfl⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_stateCount_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.stateCount
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_startField_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.startField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_haltField_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.haltField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_haltField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.haltField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_startField_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.startField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt suffix) := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨start + 1, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_done_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.haltField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.done :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_haltField_nat
                      htail with
                    ⟨halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨0, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_stateCount_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.stateCount
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt suffix)) := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨stateCount, start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨stateCount + 1, start, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_done_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.done :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_startField_fields
                      htail with
                    ⟨start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨0, start, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_needHeader_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.needHeader
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_header
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.header :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_stateCount_fields
                      htail with
                    ⟨stateCount, start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨stateCount, start, halt, parsedSuffix,
                      by simp [hsuffix]⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

/-!
**Normalizer code-spec frontier.**  The concrete
{name}`codePrefixParserNormalizerMachine` is the finite-state witness used by
the first universal-prefix scaffold.  Its remaining correctness proof is split
into soundness and completeness directions; the packaged spec below keeps
downstream construction code independent of that split.
-/

theorem codePrefixParserNormalizerMachine_haltsWithOutputIn_needHeader_fields
    {steps : Nat} {tokens out : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsWithOutputIn
        codePrefixParserNormalizerMachine steps tokens out) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  have hhalts :
      TuringMachine.HaltsOnInputIn
        codePrefixParserNormalizerMachine steps tokens :=
    TuringMachine.halts_with_output_in_implies_halts_in h
  exact
    codePrefixParserNormalizerMachine_haltsFromIn_needHeader_fields
      (steps := steps) (leftRev := []) (rest := tokens)
      (by
        simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
          codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerTape_nil_eq_input] using hhalts)

theorem codePrefixParserNormalizerMachine_haltsWithOutput_needHeader_fields
    {tokens out : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  rcases
      TuringMachine.halts_with_output_to_halts_with_output_in h with
    ⟨steps, hsteps⟩
  exact
    codePrefixParserNormalizerMachine_haltsWithOutputIn_needHeader_fields
      hsteps


end Computability
end FoC

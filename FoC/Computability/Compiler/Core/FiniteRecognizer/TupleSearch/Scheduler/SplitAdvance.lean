import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.MainRolloverRewind

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.SplitAdvance

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

inductive Control where
  | used
  | marker
  | takeRemaining
  | writeDone
  | writeTick
  | rewind (inner : RewindWord.Control)
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.used, .marker, .takeRemaining, .writeDone, .writeTick] ++
    RewindWord.Control.finite.elems.map Control.rewind
  complete := by
    intro control
    cases control with
    | used => simp
    | marker => simp
    | takeRemaining => simp
    | writeDone => simp
    | writeTick => simp
    | rewind inner =>
        simp
        exact RewindWord.Control.finite.complete inner

end Control

def mapAction (action : Option MachineCodeSymbol × Direction ×
    RewindWord.Control) :
    Option MachineCodeSymbol × Direction × Control :=
  (action.1, action.2.1, .rewind action.2.2)

def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .used, some .tick =>
      some (some .tick, Direction.right, .used)
  | .used, some .done =>
      some (some .done, Direction.right, .marker)
  | .marker, some .transition =>
      some (some .transition, Direction.right, .takeRemaining)
  | .takeRemaining, some .tick =>
      some (some .transition, Direction.left, .writeDone)
  | .writeDone, some .transition =>
      some (some .done, Direction.left, .writeTick)
  | .writeTick, some .done =>
      some (some .tick, Direction.right, .rewind .start)
  | .rewind inner, read =>
      match RewindWord.transition inner read with
      | none => none
      | some action => some (mapAction action)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .used
  halt := .rewind .gate
  transition := transition
  statesFinite := Control.finite

def ticks (count : Nat) : Word MachineCodeSymbol :=
  Scheduler.Advance.ExhaustedSplitReset.ticks count

def scanConfig (remainingUsed crossed baseRev : Word MachineCodeSymbol)
    (remaining : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .used
    tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
      (List.append crossed baseRev)
      (List.append remainingUsed
        (MachineCodeSymbol.done ::
          Scheduler.SplitLayout.splitMarker ::
          MachineCodeSymbol.tick ::
          MachineDescription.encodeNatAppend remaining suffix)) }

def sourceConfig (used remaining : Nat) (baseRev suffix :
    Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := machine.start
    tape := ExactFuel.StrictProbe.SerializedShift.cursorTape baseRev
      (Scheduler.SplitLayout.encodeSplitAppend used (remaining + 1)
        suffix) }

def rewriteTargetConfig (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rewind .start
    tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
      (MachineCodeSymbol.tick :: List.append (ticks used) baseRev)
      (MachineCodeSymbol.done ::
        Scheduler.SplitLayout.splitMarker ::
        MachineDescription.encodeNatAppend remaining suffix) }

def outputWord (used remaining : Nat) (baseRev suffix :
    Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append baseRev.reverse
    (Scheduler.SplitLayout.encodeSplitAppend (used + 1) remaining
      suffix)

theorem source_eq_scanConfig (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    sourceConfig used remaining baseRev suffix =
      scanConfig (ticks used) [] baseRev remaining suffix := by
  have hremaining :
      Scheduler.Advance.ExhaustedSplitReset.ticks (remaining + 1) =
        MachineCodeSymbol.tick ::
          Scheduler.Advance.ExhaustedSplitReset.ticks remaining := by
    simp [Scheduler.Advance.ExhaustedSplitReset.ticks,
      List.replicate_succ]
  have hword :
      Scheduler.SplitLayout.encodeSplitAppend used (remaining + 1)
          suffix =
        List.append (ticks used)
          (MachineCodeSymbol.done ::
            Scheduler.SplitLayout.splitMarker ::
            MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend remaining suffix) := by
    simp [Scheduler.SplitLayout.encodeSplitAppend,
      MachineDescription.encodeNatAppend,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      ticks, hremaining, List.append_assoc]
  unfold sourceConfig scanConfig machine
  simp only
  rw [hword]
  simp

theorem scan_tick_step (remainingUsed crossed baseRev :
    Word MachineCodeSymbol) (remaining : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanConfig (MachineCodeSymbol.tick :: remainingUsed) crossed
          baseRev remaining suffix) =
      some (scanConfig remainingUsed (MachineCodeSymbol.tick :: crossed)
        baseRev remaining suffix) := by
  cases remainingUsed <;> cases crossed <;> cases baseRev <;> rfl

theorem scan_ticks_exact (remainingUsed crossed baseRev :
    Word MachineCodeSymbol) (remaining : Nat)
    (suffix : Word MachineCodeSymbol)
    (hticks : ∀ token, List.Mem token remainingUsed ->
      token = MachineCodeSymbol.tick) :
    machine.runConfigExact? remainingUsed.length
        (scanConfig remainingUsed crossed baseRev remaining suffix) =
      some (scanConfig []
        (List.append remainingUsed.reverse crossed) baseRev remaining
        suffix) := by
  induction remainingUsed generalizing crossed with
  | nil => rfl
  | cons current rest ih =>
      have hcurrent : current = MachineCodeSymbol.tick :=
        hticks current (List.Mem.head rest)
      subst current
      have hrest : ∀ token, List.Mem token rest ->
          token = MachineCodeSymbol.tick := by
        intro token htoken
        exact hticks token (List.Mem.tail MachineCodeSymbol.tick htoken)
      change machine.runConfigExact? (rest.length + 1)
        (scanConfig (MachineCodeSymbol.tick :: rest) crossed baseRev
          remaining suffix) = _
      rw [TuringMachine.runConfigExact?, scan_tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: crossed) hrest]
      simp [List.reverse_cons, List.append_assoc]

theorem scan_used_exact (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? used (sourceConfig used remaining baseRev suffix) =
      some (scanConfig [] (ticks used) baseRev remaining suffix) := by
  rw [source_eq_scanConfig]
  simpa [ticks, Scheduler.Advance.ExhaustedSplitReset.ticks] using
    scan_ticks_exact (ticks used) [] baseRev remaining suffix (by
      intro token htoken
      exact List.eq_of_mem_replicate htoken)

theorem rewrite_finish_exact (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 5
        (scanConfig [] (ticks used) baseRev remaining suffix) =
      some (rewriteTargetConfig used remaining baseRev suffix) := by
  rw [TuringMachine.runConfigExact?]
  rw [show machine.stepConfig
      (scanConfig [] (ticks used) baseRev remaining suffix) =
    some
      { state := .marker
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (MachineCodeSymbol.done :: List.append (ticks used) baseRev)
          (Scheduler.SplitLayout.splitMarker ::
            MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend remaining suffix) } by rfl]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [show machine.stepConfig
      { state := .marker
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (MachineCodeSymbol.done :: List.append (ticks used) baseRev)
          (Scheduler.SplitLayout.splitMarker ::
            MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend remaining suffix) } =
    some
      { state := .takeRemaining
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
            List.append (ticks used) baseRev)
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend remaining suffix) } by rfl]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [show machine.stepConfig
      { state := .takeRemaining
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (Scheduler.SplitLayout.splitMarker :: MachineCodeSymbol.done ::
            List.append (ticks used) baseRev)
          (MachineCodeSymbol.tick ::
            MachineDescription.encodeNatAppend remaining suffix) } =
    some
      { state := .writeDone
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (MachineCodeSymbol.done :: List.append (ticks used) baseRev)
          (Scheduler.SplitLayout.splitMarker ::
            Scheduler.SplitLayout.splitMarker ::
            MachineDescription.encodeNatAppend remaining suffix) } by rfl]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [show machine.stepConfig
      { state := .writeDone
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (MachineCodeSymbol.done :: List.append (ticks used) baseRev)
          (Scheduler.SplitLayout.splitMarker ::
            Scheduler.SplitLayout.splitMarker ::
            MachineDescription.encodeNatAppend remaining suffix) } =
    some
      { state := .writeTick
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (List.append (ticks used) baseRev)
          (MachineCodeSymbol.done ::
            MachineCodeSymbol.done ::
            Scheduler.SplitLayout.splitMarker ::
            MachineDescription.encodeNatAppend remaining suffix) } by rfl]
  simp only
  rw [TuringMachine.runConfigExact?]
  change machine.stepConfig
      { state := .writeTick
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          (List.append (ticks used) baseRev)
          (MachineCodeSymbol.done ::
            MachineCodeSymbol.done ::
            Scheduler.SplitLayout.splitMarker ::
            MachineDescription.encodeNatAppend remaining suffix) } = _
  rfl

theorem rewrite_exact (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (used + 5)
        (sourceConfig used remaining baseRev suffix) =
      some (rewriteTargetConfig used remaining baseRev suffix) := by
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [scan_used_exact]
  simp only
  exact rewrite_finish_exact used remaining baseRev suffix

def rewindEmbed : RewindWord.Control -> Control := Control.rewind

theorem rewind_map (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rewindEmbed state) read = some (mapAction action) := by
  cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition, transition,
      rewindEmbed, mapAction]

theorem rewind_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      RewindWord.Control)
    (hstep : RewindWord.machine.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig rewindEmbed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig rewindEmbed target) := by
  cases source with
  | mk state tape =>
      cases target with
      | mk targetState targetTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [machine]
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          cases haction : RewindWord.machine.transition state
              (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              rw [haction] at hstep
              simp only at hstep
              have hmapped := rewind_map state (Tape.read tape)
                (write, direction, nextState) haction
              rw [hmapped]
              cases hstep
              rfl

theorem rewind_computes (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (rewriteTargetConfig used remaining baseRev suffix)
        { state := machine.halt, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (outputWord used remaining baseRev suffix)) targetTape := by
  let leftRev : Word MachineCodeSymbol :=
    MachineCodeSymbol.tick :: List.append (ticks used) baseRev
  let rest : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: Scheduler.SplitLayout.splitMarker ::
      MachineDescription.encodeNatAppend remaining suffix
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      (Scheduler.MainRollover.ExactRewind.run_exact leftRev rest)
      (Scheduler.MainRollover.ExactRewind.startTape_equiv_cursorTape
        leftRev rest) with
    ⟨⟨targetState, targetTape⟩, hrun, hstate, htape⟩
  simp only at hstate
  subst targetState
  have hlift :=
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      rewindEmbed rewind_step_of_some hrun
  refine ⟨targetTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hlift), ?_⟩
  have hword : List.append leftRev.reverse rest =
      outputWord used remaining baseRev suffix := by
    simp [leftRev, rest, outputWord,
      Scheduler.SplitLayout.encodeSplitAppend,
      Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
      Scheduler.Advance.ExhaustedSplitReset.ticks,
      MachineDescription.encodeNatAppend, ticks, List.reverse_append,
      List.replicate_succ', List.append_assoc]
  rw [hword] at htape
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (outputWord used remaining baseRev suffix) 0)) htape

theorem advance (used remaining : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (sourceConfig used remaining baseRev suffix)
        { state := machine.halt, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (outputWord used remaining baseRev suffix)) targetTape := by
  have hrewrite : TuringMachine.Computes machine
      (sourceConfig used remaining baseRev suffix)
      (rewriteTargetConfig used remaining baseRev suffix) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (rewrite_exact used remaining baseRev suffix))
  rcases rewind_computes used remaining baseRev suffix with
    ⟨targetTape, hrewind, htape⟩
  exact ⟨targetTape, TuringMachine.computes_trans hrewrite hrewind, htape⟩

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.SplitAdvance

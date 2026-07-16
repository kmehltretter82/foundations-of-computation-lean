import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Assembly.Basic

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace FiniteRecognizer.Interpreter.ParserAssembly

namespace TransitionParserContextTransport

def appendLeftContext
    (baseLeftRev : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := List.append tape.left (baseLeftRev.map some)
    head := tape.head
    right := tape.right }

def appendLeftContextConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (config :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state := config.state
    tape := appendLeftContext baseLeftRev config.tape }

def blankBoundaryState : TransitionListParserState -> Prop
  | TransitionListParserState.enterMarkedPosition => True
  | TransitionListParserState.returnLeft _ => True
  | _ => False

def configHasBlankBarrier
    (config :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState) : Prop :=
  (config.tape.left = [] ∧ config.tape.head = none ∧
      blankBoundaryState config.state) ∨
    exists nearerLeft : List (Option MachineCodeSymbol),
      config.tape.left = List.append nearerLeft [none]

theorem appendLeftContext_read
    (baseLeftRev : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    Tape.read (appendLeftContext baseLeftRev tape) = Tape.read tape := by
  rfl

theorem appendLeftContext_write
    (baseLeftRev : Word MachineCodeSymbol)
    (write : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    appendLeftContext baseLeftRev (Tape.write write tape) =
      Tape.write write (appendLeftContext baseLeftRev tape) := by
  rfl

theorem appendLeftContext_move_right
    (baseLeftRev : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    appendLeftContext baseLeftRev
        (Tape.move Direction.right tape) =
      Tape.move Direction.right (appendLeftContext baseLeftRev tape) := by
  rcases tape with ⟨left, head, right⟩
  cases right <;>
    simp [appendLeftContext, Tape.move, Tape.moveRight]

theorem appendLeftContext_move_left_of_nonempty
    (baseLeftRev : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hleft : tape.left ≠ []) :
    appendLeftContext baseLeftRev
        (Tape.move Direction.left tape) =
      Tape.move Direction.left (appendLeftContext baseLeftRev tape) := by
  rcases tape with ⟨left, head, right⟩
  cases left with
  | nil => exact False.elim (hleft rfl)
  | cons leftHead leftTail =>
      simp [appendLeftContext, Tape.move, Tape.moveLeft]

theorem transition_at_blank_boundary
    (state : TransitionListParserState)
    (write : Option MachineCodeSymbol)
    (dir : Direction)
    (nextState : TransitionListParserState)
    (hstate : blankBoundaryState state)
    (haction :
      transitionListParserMachine.transition state none =
        some (write, dir, nextState)) :
    write = none ∧ dir = Direction.right := by
  cases state <;>
    simp [blankBoundaryState] at hstate
  all_goals
    simp [transitionListParserMachine] at haction
  all_goals
    rcases haction with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem left_transition_enters_boundary_state
    (state : TransitionListParserState)
    (cell write : Option MachineCodeSymbol)
    (nextState : TransitionListParserState)
    (haction :
      transitionListParserMachine.transition state cell =
        some (write, Direction.left, nextState)) :
    blankBoundaryState nextState := by
  cases state
  case seekCountDone marker =>
    cases marker <;>
      cases cell with
      | none =>
          simp_all [transitionListParserMachine,
            transitionListParserKeep] <;>
            try { rcases haction with ⟨_, hnext⟩
                  subst nextState
                  trivial }
      | some symbol =>
          cases symbol <;>
            simp_all [transitionListParserMachine,
              transitionListParserKeep] <;>
            try { rcases haction with ⟨_, hnext⟩
                  subst nextState
                  trivial }
  all_goals
    cases cell with
    | none =>
        simp_all [transitionListParserMachine,
          transitionListParserKeep, blankBoundaryState] <;>
          try { rcases haction with ⟨_, hnext⟩
                subst nextState
                trivial }
    | some symbol =>
        cases symbol <;>
          simp_all [transitionListParserMachine,
            transitionListParserKeep, blankBoundaryState] <;>
          try { rcases haction with ⟨_, hnext⟩
                subst nextState
                trivial }

theorem appendLeftContext_write_move_right
    (baseLeftRev : Word MachineCodeSymbol)
    (write : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    appendLeftContext baseLeftRev
        (Tape.move Direction.right (Tape.write write tape)) =
      Tape.move Direction.right
        (Tape.write write (appendLeftContext baseLeftRev tape)) := by
  rw [appendLeftContext_move_right, appendLeftContext_write]

theorem appendLeftContext_write_move_left_of_nonempty
    (baseLeftRev : Word MachineCodeSymbol)
    (write : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hleft : tape.left ≠ []) :
    appendLeftContext baseLeftRev
        (Tape.move Direction.left (Tape.write write tape)) =
      Tape.move Direction.left
        (Tape.write write (appendLeftContext baseLeftRev tape)) := by
  rw [appendLeftContext_move_left_of_nonempty
      baseLeftRev (Tape.write write tape) (by simpa [Tape.write]),
    appendLeftContext_write]

theorem left_source_nonempty
    {source :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (write : Option MachineCodeSymbol)
    (nextState : TransitionListParserState)
    (hbarrier : configHasBlankBarrier source)
    (haction :
      transitionListParserMachine.transition source.state
          (Tape.read source.tape) =
        some (write, Direction.left, nextState)) :
    source.tape.left ≠ [] := by
  rcases hbarrier with
    ⟨hleft, hhead, hstate⟩ | ⟨nearerLeft, hleft⟩
  · have hblank :
        transitionListParserMachine.transition source.state none =
          some (write, Direction.left, nextState) := by
      simpa [Tape.read, hhead] using haction
    have hdir :=
      (transition_at_blank_boundary source.state write Direction.left
        nextState hstate hblank).2
    cases hdir
  · rw [hleft]
    simp

theorem step_preserves_blank_barrier
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hbarrier : configHasBlankBarrier source)
    (hstep : TuringMachine.Step transitionListParserMachine source target) :
    configHasBlankBarrier target := by
  cases hstep with
  | @mk write dir nextState haction =>
      cases dir with
      | left =>
          have hnext : blankBoundaryState nextState :=
            left_transition_enters_boundary_state
              source.state (Tape.read source.tape) write nextState haction
          rcases hbarrier with
            ⟨hleft, hhead, hstate⟩ | ⟨nearerLeft, hleft⟩
          · have hnonempty :=
              left_source_nonempty write nextState
                (Or.inl ⟨hleft, hhead, hstate⟩) haction
            exact False.elim (hnonempty hleft)
          · cases nearerLeft with
            | nil =>
                left
                constructor
                · simp [Tape.move, Tape.moveLeft, Tape.write, hleft]
                · constructor
                  · simp [Tape.move, Tape.moveLeft, Tape.write, hleft]
                  · exact hnext
            | cons nearerHead nearerTail =>
                right
                refine ⟨nearerTail, ?_⟩
                simp [Tape.move, Tape.moveLeft, Tape.write, hleft]
      | right =>
          rcases hbarrier with
            ⟨hleft, hhead, hstate⟩ | ⟨nearerLeft, hleft⟩
          · have hblank :
                transitionListParserMachine.transition source.state none =
                  some (write, Direction.right, nextState) := by
              simpa [Tape.read, hhead] using haction
            have hwrite :=
              (transition_at_blank_boundary source.state write
                Direction.right nextState hstate hblank).1
            subst write
            right
            refine ⟨[], ?_⟩
            cases hright : source.tape.right <;>
              simp [Tape.move, Tape.moveRight, Tape.write,
                hleft, hright]
          · right
            refine ⟨write :: nearerLeft, ?_⟩
            cases hright : source.tape.right <;>
              simp [Tape.move, Tape.moveRight, Tape.write,
                hleft, hright]

theorem step_append_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hbarrier : configHasBlankBarrier source)
    (hstep : TuringMachine.Step transitionListParserMachine source target) :
    TuringMachine.Step transitionListParserMachine
      (appendLeftContextConfig baseLeftRev source)
      (appendLeftContextConfig baseLeftRev target) := by
  cases hstep with
  | @mk write dir nextState haction =>
      cases dir with
      | left =>
          have hleft : source.tape.left ≠ [] :=
            left_source_nonempty write nextState hbarrier haction
          change
            TuringMachine.Step transitionListParserMachine
              { state := source.state
                tape := appendLeftContext baseLeftRev source.tape }
              { state := nextState
                tape :=
                  appendLeftContext baseLeftRev
                    (Tape.move Direction.left
                      (Tape.write write source.tape)) }
          rw [appendLeftContext_write_move_left_of_nonempty
            baseLeftRev write source.tape hleft]
          exact TuringMachine.Step.mk (by
            simpa [appendLeftContext, Tape.read] using haction)
      | right =>
          change
            TuringMachine.Step transitionListParserMachine
              { state := source.state
                tape := appendLeftContext baseLeftRev source.tape }
              { state := nextState
                tape :=
                  appendLeftContext baseLeftRev
                    (Tape.move Direction.right
                      (Tape.write write source.tape)) }
          rw [appendLeftContext_write_move_right]
          exact TuringMachine.Step.mk (by
            simpa [appendLeftContext, Tape.read] using haction)

theorem computes_append_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hbarrier : configHasBlankBarrier source)
    (hrun : TuringMachine.Computes transitionListParserMachine source target) :
    TuringMachine.Computes transitionListParserMachine
      (appendLeftContextConfig baseLeftRev source)
      (appendLeftContextConfig baseLeftRev target) := by
  revert hbarrier
  induction hrun with
  | refl config =>
      intro hbarrier
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      intro hbarrier
      have hnextBarrier := step_preserves_blank_barrier hbarrier hstep
      exact
        TuringMachine.Computes.step
          (step_append_left_context baseLeftRev hbarrier hstep)
          (ih hnextBarrier)

theorem computes_preserves_blank_barrier
    {source target :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hbarrier : configHasBlankBarrier source)
    (hrun : TuringMachine.Computes transitionListParserMachine source target) :
    configHasBlankBarrier target := by
  induction hrun with
  | refl config => exact hbarrier
  | step hstep hrest ih =>
      exact ih (step_preserves_blank_barrier hbarrier hstep)

def canonicalWord
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend transitions.length
    (MachineDescription.encodeTransitionsAppend transitions suffix)

def paddedCanonicalSource
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  { state :=
      TransitionListParserState.findCount
        TransitionListParserMarker.initial
    tape :=
      transitionListParserOptionTape [none]
        ((canonicalWord transitions suffix).map some) }

def contextualCanonicalSource
    (baseLeftRev : Word MachineCodeSymbol)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      TransitionListParserState :=
  appendLeftContextConfig baseLeftRev
    (paddedCanonicalSource transitions suffix)

theorem paddedCanonicalSource_has_barrier
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    configHasBlankBarrier (paddedCanonicalSource transitions suffix) := by
  right
  cases hword : canonicalWord transitions suffix <;>
    refine ⟨[], ?_⟩ <;>
    simp [paddedCanonicalSource, transitionListParserOptionTape, hword]

theorem cleanCanonicalSource_tape_equiv_padded
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    Tape.Equiv
      (TuringMachine.initial transitionListParserMachine
        (canonicalWord transitions suffix)).tape
      (paddedCanonicalSource transitions suffix).tape := by
  simpa [canonicalWord, paddedCanonicalSource,
    TuringMachine.initial, transitionListParserMachine,
    transitionListParserOptionTape_nil_eq_input] using
      transitionListParserOptionTape_append_none_equiv
        ([] : List (Option MachineCodeSymbol))
        ((canonicalWord transitions suffix).map some)

theorem paddedCanonicalSource_parser_forward
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    ParserRunsToEquiv
      (paddedCanonicalSource transitions suffix)
      (canonicalTransitionParserHaltConfig transitions suffix) := by
  have hpad :
      ParserRunsToEquiv
        (paddedCanonicalSource transitions suffix)
        (TuringMachine.initial transitionListParserMachine
          (canonicalWord transitions suffix)) :=
    ParserRunsToEquiv.sourceEquiv rfl
      (cleanCanonicalSource_tape_equiv_padded transitions suffix)
  have hclean :=
    transitionListParserMachine_runs_encodeTransitions_to_equiv
      transitions suffix
  change
    ParserRunsToEquiv
      (TuringMachine.initial transitionListParserMachine
        (canonicalWord transitions suffix))
      (canonicalTransitionParserHaltConfig transitions suffix) at hclean
  exact ParserRunsToEquiv.trans hpad hclean

/-- Uniform contextual 0/1/N transition parsing.  The actual endpoint is the
clean padded run endpoint with the retained header/fuel context appended beyond
its preserved blank barrier. -/
theorem contextualCanonicalSource_parser_forward
    (baseLeftRev : Word MachineCodeSymbol)
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    exists cleanEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Computes transitionListParserMachine
          (contextualCanonicalSource baseLeftRev transitions suffix)
          (appendLeftContextConfig baseLeftRev cleanEndpoint) ∧
      cleanEndpoint.state =
        (canonicalTransitionParserHaltConfig transitions suffix).state ∧
      Tape.Equiv
        (canonicalTransitionParserHaltConfig transitions suffix).tape
        cleanEndpoint.tape ∧
      configHasBlankBarrier cleanEndpoint := by
  rcases paddedCanonicalSource_parser_forward transitions suffix with
    ⟨cleanEndpoint, hrun, hstate, htape⟩
  have hsourceBarrier :=
    paddedCanonicalSource_has_barrier transitions suffix
  have hendpointBarrier :=
    computes_preserves_blank_barrier hsourceBarrier hrun
  refine ⟨cleanEndpoint, ?_, hstate, htape, hendpointBarrier⟩
  exact computes_append_left_context baseLeftRev hsourceBarrier hrun

/-- Remove an inert far-left context from one parser step.  The blank barrier
guarantees that a left-moving action has a genuine near-side predecessor, so
the contextual step cannot consume a retained metadata cell. -/
theorem step_remove_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source contextualTarget :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hbarrier : configHasBlankBarrier source)
    (hstep :
      TuringMachine.Step transitionListParserMachine
        (appendLeftContextConfig baseLeftRev source)
        contextualTarget) :
    exists target :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Step transitionListParserMachine source target ∧
      contextualTarget = appendLeftContextConfig baseLeftRev target ∧
      configHasBlankBarrier target := by
  cases hstep with
  | @mk write dir nextState haction =>
      have hactionClean :
          transitionListParserMachine.transition source.state
              (Tape.read source.tape) =
            some (write, dir, nextState) := by
        simpa [appendLeftContextConfig, appendLeftContext, Tape.read]
          using haction
      let target :
          TuringMachine.Configuration MachineCodeSymbol
            TransitionListParserState :=
        { state := nextState
          tape := Tape.move dir (Tape.write write source.tape) }
      have hclean :
          TuringMachine.Step transitionListParserMachine source target := by
        exact TuringMachine.Step.mk hactionClean
      refine
        ⟨target, hclean, ?_,
          step_preserves_blank_barrier hbarrier hclean⟩
      cases dir with
      | left =>
          have hleft : source.tape.left ≠ [] :=
            left_source_nonempty write nextState hbarrier hactionClean
          simpa [appendLeftContextConfig, target] using
            congrArg
              (fun tape : Tape MachineCodeSymbol =>
                ({ state := nextState, tape := tape } :
                  TuringMachine.Configuration MachineCodeSymbol
                    TransitionListParserState))
              (Eq.symm
                (appendLeftContext_write_move_left_of_nonempty
                  baseLeftRev write source.tape hleft))
      | right =>
          simpa [appendLeftContextConfig, target] using
            congrArg
              (fun tape : Tape MachineCodeSymbol =>
                ({ state := nextState, tape := tape } :
                  TuringMachine.Configuration MachineCodeSymbol
                    TransitionListParserState))
              (Eq.symm
                (appendLeftContext_write_move_right
                  baseLeftRev write source.tape))

/-- Project a whole contextual parser run to the barrier-delimited clean run,
recovering the retained far-left context exactly at the endpoint. -/
theorem computes_remove_left_context_of_eq
    (baseLeftRev : Word MachineCodeSymbol)
    {source contextualSource contextualTarget :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hsource :
      contextualSource = appendLeftContextConfig baseLeftRev source)
    (hbarrier : configHasBlankBarrier source)
    (hrun :
      TuringMachine.Computes transitionListParserMachine
        contextualSource contextualTarget) :
    exists target :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Computes transitionListParserMachine source target ∧
      contextualTarget = appendLeftContextConfig baseLeftRev target ∧
      configHasBlankBarrier target := by
  induction hrun generalizing source with
  | refl contextualSource =>
      exact ⟨source, TuringMachine.Computes.refl _, hsource, hbarrier⟩
  | @step contextualSource contextualNext contextualTarget
      hstep hrest ih =>
      have hstep' :
          TuringMachine.Step transitionListParserMachine
            (appendLeftContextConfig baseLeftRev source)
            contextualNext := by
        simpa [← hsource] using hstep
      rcases step_remove_left_context baseLeftRev hbarrier hstep' with
        ⟨next, hnext, hcontextualNext, hnextBarrier⟩
      rcases ih hcontextualNext hnextBarrier with
        ⟨target, htail, htarget, htargetBarrier⟩
      exact
        ⟨target, TuringMachine.Computes.step hnext htail,
          htarget, htargetBarrier⟩

theorem computes_remove_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source contextualTarget :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState}
    (hbarrier : configHasBlankBarrier source)
    (hrun :
      TuringMachine.Computes transitionListParserMachine
        (appendLeftContextConfig baseLeftRev source)
        contextualTarget) :
    exists target :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
      TuringMachine.Computes transitionListParserMachine source target ∧
      contextualTarget = appendLeftContextConfig baseLeftRev target ∧
      configHasBlankBarrier target :=
  computes_remove_left_context_of_eq baseLeftRev rfl hbarrier hrun

end TransitionParserContextTransport

namespace MarkerRestoreContextTransport

def appendLeftContextConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (config :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState) :
    TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState :=
  { state := config.state
    tape :=
      TransitionParserContextTransport.appendLeftContext
        baseLeftRev config.tape }

def blankBoundaryState : MarkerRestoreState -> Prop
  | MarkerRestoreState.rewind => True
  | _ => False

def configHasBlankBarrier
    (config :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState) :
    Prop :=
  (config.tape.left = [] ∧ config.tape.head = none ∧
      blankBoundaryState config.state) ∨
    exists nearerLeft : List (Option MachineCodeSymbol),
      config.tape.left = List.append nearerLeft [none]

theorem transition_at_blank_boundary
    (state : MarkerRestoreState)
    (write : Option MachineCodeSymbol)
    (dir : Direction)
    (nextState : MarkerRestoreState)
    (hstate : blankBoundaryState state)
    (haction :
      markerRestoreMachine.transition state none =
        some (write, dir, nextState)) :
    write = none ∧ dir = Direction.right := by
  cases state <;> simp [blankBoundaryState] at hstate
  simp [markerRestoreMachine] at haction
  rcases haction with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem left_transition_enters_boundary_state
    (state : MarkerRestoreState)
    (cell write : Option MachineCodeSymbol)
    (nextState : MarkerRestoreState)
    (haction :
      markerRestoreMachine.transition state cell =
        some (write, Direction.left, nextState)) :
    blankBoundaryState nextState := by
  cases state <;>
    cases cell with
    | none =>
        simp_all [markerRestoreMachine] <;>
          try { rcases haction with ⟨_, hnext⟩
                subst nextState
                trivial }
    | some symbol =>
        cases symbol <;>
          simp_all [markerRestoreMachine, blankBoundaryState] <;>
          try { rcases haction with ⟨_, hnext⟩
                subst nextState
                trivial }

theorem left_source_nonempty
    {source :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState}
    (write : Option MachineCodeSymbol)
    (nextState : MarkerRestoreState)
    (hbarrier : configHasBlankBarrier source)
    (haction :
      markerRestoreMachine.transition source.state
          (Tape.read source.tape) =
        some (write, Direction.left, nextState)) :
    source.tape.left ≠ [] := by
  rcases hbarrier with
    ⟨hleft, hhead, hstate⟩ | ⟨nearerLeft, hleft⟩
  · have hblank :
        markerRestoreMachine.transition source.state none =
          some (write, Direction.left, nextState) := by
      simpa [Tape.read, hhead] using haction
    have hdir :=
      (transition_at_blank_boundary source.state write Direction.left
        nextState hstate hblank).2
    cases hdir
  · rw [hleft]
    simp

theorem step_preserves_blank_barrier
    {source target :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState}
    (hbarrier : configHasBlankBarrier source)
    (hstep : TuringMachine.Step markerRestoreMachine source target) :
    configHasBlankBarrier target := by
  cases hstep with
  | @mk write dir nextState haction =>
      cases dir with
      | left =>
          have hnext : blankBoundaryState nextState :=
            left_transition_enters_boundary_state
              source.state (Tape.read source.tape) write nextState haction
          rcases hbarrier with
            ⟨hleft, hhead, hstate⟩ | ⟨nearerLeft, hleft⟩
          · have hnonempty :=
              left_source_nonempty write nextState
                (Or.inl ⟨hleft, hhead, hstate⟩) haction
            exact False.elim (hnonempty hleft)
          · cases nearerLeft with
            | nil =>
                left
                constructor
                · simp [Tape.move, Tape.moveLeft, Tape.write, hleft]
                · constructor
                  · simp [Tape.move, Tape.moveLeft, Tape.write, hleft]
                  · exact hnext
            | cons nearerHead nearerTail =>
                right
                refine ⟨nearerTail, ?_⟩
                simp [Tape.move, Tape.moveLeft, Tape.write, hleft]
      | right =>
          rcases hbarrier with
            ⟨hleft, hhead, hstate⟩ | ⟨nearerLeft, hleft⟩
          · have hblank :
                markerRestoreMachine.transition source.state none =
                  some (write, Direction.right, nextState) := by
              simpa [Tape.read, hhead] using haction
            have hwrite :=
              (transition_at_blank_boundary source.state write
                Direction.right nextState hstate hblank).1
            subst write
            right
            refine ⟨[], ?_⟩
            cases hright : source.tape.right <;>
              simp [Tape.move, Tape.moveRight, Tape.write,
                hleft, hright]
          · right
            refine ⟨write :: nearerLeft, ?_⟩
            cases hright : source.tape.right <;>
              simp [Tape.move, Tape.moveRight, Tape.write,
                hleft, hright]

theorem step_append_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState}
    (hbarrier : configHasBlankBarrier source)
    (hstep : TuringMachine.Step markerRestoreMachine source target) :
    TuringMachine.Step markerRestoreMachine
      (appendLeftContextConfig baseLeftRev source)
      (appendLeftContextConfig baseLeftRev target) := by
  cases hstep with
  | @mk write dir nextState haction =>
      cases dir with
      | left =>
          have hleft : source.tape.left ≠ [] :=
            left_source_nonempty write nextState hbarrier haction
          change
            TuringMachine.Step markerRestoreMachine
              { state := source.state
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev source.tape }
              { state := nextState
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev
                    (Tape.move Direction.left
                      (Tape.write write source.tape)) }
          rw [TransitionParserContextTransport.appendLeftContext_write_move_left_of_nonempty
            baseLeftRev write source.tape hleft]
          exact TuringMachine.Step.mk (by
            simpa [TransitionParserContextTransport.appendLeftContext,
              Tape.read] using haction)
      | right =>
          change
            TuringMachine.Step markerRestoreMachine
              { state := source.state
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev source.tape }
              { state := nextState
                tape :=
                  TransitionParserContextTransport.appendLeftContext
                    baseLeftRev
                    (Tape.move Direction.right
                      (Tape.write write source.tape)) }
          rw [TransitionParserContextTransport.appendLeftContext_write_move_right]
          exact TuringMachine.Step.mk (by
            simpa [TransitionParserContextTransport.appendLeftContext,
              Tape.read] using haction)

theorem computes_append_left_context
    (baseLeftRev : Word MachineCodeSymbol)
    {source target :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState}
    (hbarrier : configHasBlankBarrier source)
    (hrun : TuringMachine.Computes markerRestoreMachine source target) :
    TuringMachine.Computes markerRestoreMachine
      (appendLeftContextConfig baseLeftRev source)
      (appendLeftContextConfig baseLeftRev target) := by
  revert hbarrier
  induction hrun with
  | refl config =>
      intro hbarrier
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      intro hbarrier
      have hnextBarrier := step_preserves_blank_barrier hbarrier hstep
      exact
        TuringMachine.Computes.step
          (step_append_left_context baseLeftRev hbarrier hstep)
          (ih hnextBarrier)

theorem computes_preserves_blank_barrier
    {source target :
      TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState}
    (hbarrier : configHasBlankBarrier source)
    (hrun : TuringMachine.Computes markerRestoreMachine source target) :
    configHasBlankBarrier target := by
  induction hrun with
  | refl config => exact hbarrier
  | step hstep hrest ih =>
      exact ih (step_preserves_blank_barrier hbarrier hstep)

theorem source_barrier_of_parser_halt_barrier
    (parserEndpoint :
      TuringMachine.Configuration MachineCodeSymbol
        TransitionListParserState)
    (saved : Option MachineCodeSymbol)
    (hstate : parserEndpoint.state = TransitionListParserState.halt)
    (hbarrier :
      TransitionParserContextTransport.configHasBlankBarrier
        parserEndpoint) :
    configHasBlankBarrier
      { state := MarkerRestoreState.seek saved
        tape := parserEndpoint.tape } := by
  rcases hbarrier with
    ⟨hleft, hhead, hboundary⟩ | ⟨nearerLeft, hleft⟩
  · rw [hstate] at hboundary
    simp [TransitionParserContextTransport.blankBoundaryState] at hboundary
  · right
    exact ⟨nearerLeft, hleft⟩

/-- Contextual parser plus marker restoration for every nonempty canonical
transition table.  Both actual phases retain the same far-left header/fuel
context behind the physical blank separator. -/
theorem contextualNonemptyParserRestorer_forward
    (baseLeftRev : Word MachineCodeSymbol)
    (t : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    exists parserEndpoint :
        TuringMachine.Configuration MachineCodeSymbol
          TransitionListParserState,
    exists markerEndpoint :
        TuringMachine.Configuration MachineCodeSymbol MarkerRestoreState,
      TuringMachine.Computes transitionListParserMachine
          (TransitionParserContextTransport.contextualCanonicalSource
            baseLeftRev (t :: rest) suffix)
          (TransitionParserContextTransport.appendLeftContextConfig
            baseLeftRev parserEndpoint) ∧
      parserEndpoint.state = TransitionListParserState.halt ∧
      Tape.Equiv
          (parsedTransitionHaltConfig (t :: rest).length
            (MachineDescription.encodeTransitions (t :: rest)) suffix).tape
          parserEndpoint.tape ∧
      TuringMachine.Computes markerRestoreMachine
          (appendLeftContextConfig baseLeftRev
            { state :=
                MarkerRestoreState.seek
                  (transitionListParserSavedHead suffix)
              tape := parserEndpoint.tape })
          (appendLeftContextConfig baseLeftRev markerEndpoint) ∧
      markerEndpoint.state = MarkerRestoreState.halt ∧
      Tape.Equiv
          (parsedMarkerRestoreTargetConfig (t :: rest).length
            (MachineDescription.encodeTransitions (t :: rest)) suffix).tape
          markerEndpoint.tape := by
  rcases
      TransitionParserContextTransport.contextualCanonicalSource_parser_forward
        baseLeftRev (t :: rest) suffix with
    ⟨parserEndpoint, hparser, hparserState,
      hparserTape, hparserBarrier⟩
  have hparserState' :
      parserEndpoint.state = TransitionListParserState.halt := by
    simpa [canonicalTransitionParserHaltConfig,
      parsedTransitionHaltConfig] using hparserState
  have hparserTape' :
      Tape.Equiv
        (parsedTransitionHaltConfig (t :: rest).length
          (MachineDescription.encodeTransitions (t :: rest)) suffix).tape
        parserEndpoint.tape := by
    simpa [canonicalTransitionParserHaltConfig] using hparserTape
  have hsymbols :
      transitionListParserNoHeader
        (MachineDescription.encodeTransitions (t :: rest)) := by
    simpa [MachineDescription.encodeTransitions] using
      transitionListParser_encodeTransitionsAppend_noHeader
        (t :: rest) (suffix := []) (by
          intro symbol hmem
          simp at hmem)
  have hsymbolsNonempty :
      MachineDescription.encodeTransitions (t :: rest) ≠ [] := by
    simp [MachineDescription.encodeTransitions,
      MachineDescription.encodeTransitionsAppend,
      MachineDescription.encodeTransitionAppend]
  have hmarker :=
    markerRestoreMachine_runs_parsed_to_equiv rest.length
      (MachineDescription.encodeTransitions (t :: rest)) suffix
      hsymbols hsymbolsNonempty (by
        simpa using hparserTape')
  rcases hmarker with
    ⟨markerEndpoint, hmarkerRun, hmarkerState, hmarkerTape⟩
  have hmarkerSourceBarrier :=
    source_barrier_of_parser_halt_barrier parserEndpoint
      (transitionListParserSavedHead suffix)
      hparserState' hparserBarrier
  have hmarkerRunContext :=
    computes_append_left_context baseLeftRev
      hmarkerSourceBarrier hmarkerRun
  refine
    ⟨parserEndpoint, markerEndpoint, hparser, hparserState',
      hparserTape', hmarkerRunContext, ?_, ?_⟩
  · simpa [parsedMarkerRestoreTargetConfig] using hmarkerState
  · simpa using hmarkerTape

end MarkerRestoreContextTransport

end FiniteRecognizer.Interpreter.ParserAssembly
end Computability
end FoC

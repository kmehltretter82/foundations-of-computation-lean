import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.LoopRestagingAudit

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair

/-!
**Bounded-interpreter loop currency.** The invariant stores one raw
transition-table copy for each unexecuted semantic step. A header separates
adjacent copies, and a double header terminates the stack before the mutable
tape contexts. The empty-table case uses a separate branch, because an empty
next copy is otherwise indistinguishable from the double-header sentinel.
Initialization constructs the stack once; each runtime iteration performs
context update followed by front restaging.
-/

/-- Raw transition-table word, excluding every stack delimiter. -/
def rawTable
    (transitions : List TransitionDescription) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeTransitions transitions

/-- `copies` raw tables, each followed by one delimiter, followed by the
second sentinel delimiter. -/
def tableStack
    (transitions : List TransitionDescription) :
    Nat -> Word MachineCodeSymbol
  | 0 => [MachineCodeSymbol.header]
  | copies + 1 =>
      MachineDescription.encodeTransitionsAppend transitions
        (MachineCodeSymbol.header :: tableStack transitions copies)

theorem tableStack_zero
    (transitions : List TransitionDescription) :
    tableStack transitions 0 = [MachineCodeSymbol.header] := by
  rfl
  done

theorem tableStack_succ
    (transitions : List TransitionDescription)
    (copies : Nat) :
    tableStack transitions (copies + 1) =
      List.append (rawTable transitions)
        (MachineCodeSymbol.header :: tableStack transitions copies) := by
  change
    (show List MachineCodeSymbol from
      MachineDescription.encodeTransitionsAppend transitions
        (MachineCodeSymbol.header :: tableStack transitions copies)) =
      List.append
        (show List MachineCodeSymbol from rawTable transitions)
        (MachineCodeSymbol.header :: tableStack transitions copies)
  simpa [rawTable, MachineDescription.encodeTransitions] using
    (MachineDescription.encodeTransitionsAppend_append transitions []
      (MachineCodeSymbol.header :: tableStack transitions copies)).symm
  done

theorem tableStack_nonempty_copy_starts_transition
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat) :
    tableStack (first :: rest) (copies + 1) =
      MachineCodeSymbol.transition ::
        runtimeKeyRawTransitionTail first rest
          (MachineCodeSymbol.header ::
            tableStack (first :: rest) copies) := by
  rfl
  done

/-- The payload behind the stack sentinel.  The halt state stays serialized;
the current state never enters finite control. -/
def contextTail
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  protectedTapeContextsAppend tape
    (MachineDescription.encodeNatAppend haltState callerSuffix)

/-- Caller-owned suffix protected by the active table scan. -/
def activeProtectedSuffix
    (transitions : List TransitionDescription)
    (remainingCopies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (tableStack transitions remainingCopies)
    (contextTail tape haltState callerSuffix)

/-- Exact scan word for one active table plus a stack of later copies. -/
def scanWord
    (current : MachineDescription.Configuration)
    (transitions : List TransitionDescription)
    (remainingCopies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append
      (runtimeKeyBuilderKeyCode current.state (Tape.read current.tape))
      (MachineDescription.encodeTransitionsAppend transitions
        (MachineCodeSymbol.header ::
          activeProtectedSuffix transitions remainingCopies current.tape
            haltState callerSuffix))

theorem scanWord_is_single_key_currency
    (current : MachineDescription.Configuration)
    (transitions : List TransitionDescription)
    (remainingCopies : Nat)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    scanWord current transitions remainingCopies haltState callerSuffix =
      MachineCodeSymbol.header ::
        List.append
          (runtimeKeyBuilderKeyCode current.state (Tape.read current.tape))
          (MachineDescription.encodeTransitionsAppend transitions
            (MachineCodeSymbol.header ::
              activeProtectedSuffix transitions remainingCopies current.tape
                haltState callerSuffix)) := by
  rfl
  done

/-- Successful selected-row cleanup produces the context-update source. The
active copy is absent, and the unused table copies precede the contexts. -/
def postSelectedWord
    (target : Nat)
    (transitions : List TransitionDescription)
    (remainingCopies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend target
    (MachineCodeSymbol.header ::
      activeProtectedSuffix transitions remainingCopies tape haltState
        callerSuffix)

theorem postSelectedWord_zero_has_double_header
    (target : Nat)
    (transitions : List TransitionDescription)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    postSelectedWord target transitions 0 tape haltState callerSuffix =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
          contextTail tape haltState callerSuffix) := by
  rfl
  done

theorem postSelectedWord_succ_exposes_next_table
    (target : Nat)
    (transitions : List TransitionDescription)
    (copies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    postSelectedWord target transitions (copies + 1) tape haltState
        callerSuffix =
      MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          MachineDescription.encodeTransitionsAppend transitions
            (MachineCodeSymbol.header ::
              List.append (tableStack transitions copies)
                (contextTail tape haltState callerSuffix))) := by
  change
    MachineDescription.encodeNatAppend target
        (MachineCodeSymbol.header ::
          List.append
            (MachineDescription.encodeTransitionsAppend transitions
              (MachineCodeSymbol.header :: tableStack transitions copies))
            (contextTail tape haltState callerSuffix)) = _
  rw [MachineDescription.encodeTransitionsAppend_append]
  rfl
  done

/-!
### Empty-table collision

For an empty transition list, a stored copy contributes no symbol before its
delimiter.  Consequently one empty copy and the zero-copy sentinel have the
same leading symbol, so a finite delimiter scan cannot decide which case it
has reached.  The outer parser must branch on transition count zero and use
the semantic stutter rule directly.
-/

theorem empty_table_stack_succ
    (copies : Nat) :
    tableStack [] (copies + 1) =
      MachineCodeSymbol.header :: tableStack [] copies := by
  rfl
  done

theorem empty_table_zero_and_one_share_double_header_prefix :
    (tableStack [] 0).take 1 =
        [MachineCodeSymbol.header] /\
      (tableStack [] 1).take 2 =
        [MachineCodeSymbol.header, MachineCodeSymbol.header] := by
  constructor <;> rfl
  done

/-!
### Exact semantic gates

The physical stack is unnecessary in the two base cases.  Zero fuel performs
no description step.  An empty transition table stutters for every fuel, so
both cases reduce to comparing the current state with the serialized halt
state.
-/

theorem runConfig_zero
    (D : MachineDescription)
    (config : MachineDescription.Configuration) :
    D.runConfig 0 config = config := by
  rfl
  done

theorem runConfig_empty_transitions
    (D : MachineDescription)
    (fuel : Nat)
    (config : MachineDescription.Configuration) :
    ({ D with transitions := [] }).runConfig fuel config = config := by
  cases fuel with
  | zero => rfl
  | succ remaining =>
      apply runConfig_fullScanNoMatch
      intro transition hmem
      simp at hmem
  done

theorem empty_transitions_final_state_iff
    (D : MachineDescription)
    (fuel : Nat)
    (config : MachineDescription.Configuration) :
    (({ D with transitions := [] }).runConfig fuel config).state = D.halt <->
      config.state = D.halt := by
  rw [runConfig_empty_transitions]
  done

theorem no_match_may_discard_remaining_stack
    (D : MachineDescription)
    (remaining : Nat)
    (config : MachineDescription.Configuration)
    (hmiss :
      forall transition : TransitionDescription,
        List.Mem transition D.transitions ->
          MachineDescription.Matches config.state (Tape.read config.tape)
            transition = false) :
    (D.runConfig (remaining + 1) config).state = D.halt <->
      config.state = D.halt := by
  rw [runConfig_fullScanNoMatch D remaining config hmiss]
  done

/-!
### One exact initializer-copy seam

`ProductDuplicator` leaves a physical blank between the retained source table
and its fresh copy.  For a nonempty table, the following two-step phase writes
the logical stack delimiter into that gap and returns to the first symbol of
the fresh copy.  Its endpoint is exactly another `ProductDuplicator` source,
with the old table and delimiter absorbed into `baseLeftRev`.
-/

namespace GapHeaderSealer

inductive Control where
  | enter
  | seal
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control := [.enter, .seal, .ready, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter, read => some (read, Direction.left, .seal)
  | .seal, none =>
      some (some MachineCodeSymbol.header, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .enter
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .enter
  tape := ProductDuplicator.haltTape baseLeftRev (first :: rest)

def nextBaseLeftRev
    (baseLeftRev table : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append table.reverse baseLeftRev

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape :=
    { left :=
        (nextBaseLeftRev baseLeftRev (first :: rest)).map some
      head := some first
      right := rest.map some }

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (sourceConfig baseLeftRev first rest) =
      some (targetConfig baseLeftRev first rest) := by
  cases rest <;>
    simp [sourceConfig, targetConfig, nextBaseLeftRev,
      machine, transition, TuringMachine.runConfigExact?,
      TuringMachine.stepConfig, Tape.read,
      ProductDuplicator.haltTape, ProductDuplicator.scanTape,
      ProductDuplicator.tapeAtCells, Tape.move, Tape.moveRight,
      Tape.moveLeft, Tape.write, List.reverse_cons, List.map_append,
      List.append_assoc]
  done

theorem product_target_tape_eq_source
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    (ProductDuplicator.haltConfig baseLeftRev (first :: rest)).tape =
      (sourceConfig baseLeftRev first rest).tape := by
  rfl
  done

theorem target_tape_equiv_next_product_source
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.Equiv (targetConfig baseLeftRev first rest).tape
      (ProductDuplicator.sourceConfig
        (nextBaseLeftRev baseLeftRev (first :: rest))
        (first :: rest)).tape := by
  simp [targetConfig, ProductDuplicator.sourceConfig,
    ProductDuplicator.sourceTape, ProductDuplicator.scanConfig,
    ProductDuplicator.scanTape, ProductDuplicator.tapeAtCells,
    Tape.Equiv, FoC.Computability.dropTrailingNone_append_none]
  done

/-- One duplication iteration preserves arbitrary baseLeftRev, including
parsed caller material to the physical left. -/
theorem duplicate_and_seal_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    ProductDuplicator.machine.runConfigExact?
        (ProductDuplicator.runSteps (first :: rest))
        (ProductDuplicator.sourceConfig baseLeftRev (first :: rest)) =
      some (ProductDuplicator.haltConfig baseLeftRev (first :: rest)) /\
    machine.runConfigExact? 2
        (sourceConfig baseLeftRev first rest) =
      some (targetConfig baseLeftRev first rest) /\
    Tape.Equiv (targetConfig baseLeftRev first rest).tape
      (ProductDuplicator.sourceConfig
        (nextBaseLeftRev baseLeftRev (first :: rest))
        (first :: rest)).tape := by
  exact ⟨ProductDuplicator.run_exact baseLeftRev (first :: rest),
    run_exact baseLeftRev first rest,
    target_tape_equiv_next_product_source baseLeftRev first rest⟩
  done

end GapHeaderSealer

/-!
### Front-local next-copy restager

After context update, the source begins

`encodeNat target ++ header ++ nextRawTable ++ ...`.

The machine rewrites that delimiter to the finite next-head symbol, rewinds
over the unary target, and writes the leading scan guard into the blank just
left of the word.  It never carries `target` in finite control and never
crosses the next table or the protected contexts.
-/

namespace NextCopyRestager

inductive Control where
  | target (nextHead : Option Bool)
  | delimiter (nextHead : Option Bool)
  | rewind (nextHead : Option Bool)
  | ready (nextHead : Option Bool)
  | halt
deriving DecidableEq

namespace Control

def optionBools : List (Option Bool) :=
  [none, some false, some true]

theorem optionBools_complete
    (cell : Option Bool) :
    cell ∈ optionBools := by
  cases cell with
  | none => simp [optionBools]
  | some bit => cases bit <;> simp [optionBools]
  done

def elems : List Control :=
  optionBools.map target ++
    optionBools.map delimiter ++
    optionBools.map rewind ++
    optionBools.map ready ++ [halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | target nextHead => simp [elems, optionBools_complete nextHead]
    | delimiter nextHead => simp [elems, optionBools_complete nextHead]
    | rewind nextHead => simp [elems, optionBools_complete nextHead]
    | ready nextHead => simp [elems, optionBools_complete nextHead]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .target nextHead, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .target nextHead)
  | .target nextHead, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .delimiter nextHead)
  | .delimiter nextHead, some MachineCodeSymbol.header =>
      some (some (runtimeKeyCellSymbol nextHead), Direction.left,
        .rewind nextHead)
  | .rewind nextHead, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .rewind nextHead)
  | .rewind nextHead, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .rewind nextHead)
  | .rewind nextHead, none =>
      some (some MachineCodeSymbol.header, Direction.right, .ready nextHead)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .target none
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (nextHead : Option Bool)
    (target : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .target nextHead
  tape := SerializedShift.cursorTape []
    (MachineDescription.encodeNatAppend target
      (MachineCodeSymbol.header :: rest))

def delimiterConfig
    (nextHead : Option Bool)
    (target : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .delimiter nextHead
  tape := SerializedShift.cursorTape
    (MachineDescription.encodeNat target).reverse
    (MachineCodeSymbol.header :: rest)

def rewindConfig
    (nextHead : Option Bool)
    (remainingRev crossed : Word MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewind nextHead
  tape := match remainingRev with
    | [] =>
        { left := []
          head := none
          right :=
            (List.append crossed
              (runtimeKeyCellSymbol nextHead :: rest)).map some }
    | current :: more =>
        { left := more.map some
          head := some current
          right :=
            (List.append crossed
              (runtimeKeyCellSymbol nextHead :: rest)).map some }

def targetConfig
    (nextHead : Option Bool)
    (target : Nat)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready nextHead
  tape := SerializedShift.cursorTape [MachineCodeSymbol.header]
    (List.append (runtimeKeyBuilderKeyCode target nextHead) rest)

theorem step_target_tick
    (nextHead : Option Bool)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.target nextHead
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: rest) } =
      some
        { state := Control.target nextHead
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) rest } := by
  cases rest <;> cases leftRev <;> rfl
  done

theorem step_target_done
    (nextHead : Option Bool)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.target nextHead
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: rest) } =
      some
        { state := Control.delimiter nextHead
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) rest } := by
  cases rest <;> cases leftRev <;> rfl
  done

theorem step_delimiter
    (nextHead : Option Bool)
    (current : MachineCodeSymbol)
    (more rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := Control.delimiter nextHead
          tape := SerializedShift.cursorTape (current :: more)
            (MachineCodeSymbol.header :: rest) } =
      some
        (rewindConfig nextHead (current :: more) [] rest) := by
  cases nextHead with
  | none => cases rest <;> cases more <;> cases current <;> rfl
  | some bit =>
      cases bit <;> cases rest <;> cases more <;> cases current <;> rfl
  done

theorem step_rewind_symbol
    (nextHead : Option Bool)
    (current : MachineCodeSymbol)
    (remainingRev crossed rest : Word MachineCodeSymbol)
    (hcurrent : current = MachineCodeSymbol.tick ∨
      current = MachineCodeSymbol.done) :
    machine.stepConfig
        (rewindConfig nextHead (current :: remainingRev) crossed rest) =
      some
        (rewindConfig nextHead remainingRev (current :: crossed) rest) := by
  rcases hcurrent with rfl | rfl <;>
    cases remainingRev <;> cases crossed <;> cases rest <;>
      cases nextHead <;> try { rfl } <;>
      rename_i bit <;> cases bit <;> rfl
  done

theorem step_rewind_blank
    (nextHead : Option Bool)
    (crossed rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig nextHead [] crossed rest) =
      some
        { state := Control.ready nextHead
          tape := SerializedShift.cursorTape [MachineCodeSymbol.header]
            (List.append crossed
              (runtimeKeyCellSymbol nextHead :: rest)) } := by
  cases crossed <;> cases rest <;>
    cases nextHead <;> try { rfl } <;>
    rename_i bit <;> cases bit <;> rfl
  done

theorem run_target
    (nextHead : Option Bool)
    (target : Nat)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (target + 1)
        { state := Control.target nextHead
          tape := SerializedShift.cursorTape leftRev
            (MachineDescription.encodeNatAppend target rest) } =
      some
        { state := Control.delimiter nextHead
          tape := SerializedShift.cursorTape
            (List.append (MachineDescription.encodeNat target).reverse
              leftRev) rest } := by
  induction target generalizing leftRev with
  | zero =>
      change machine.runConfigExact? 1
        { state := Control.target nextHead
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: rest) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_target_done]
      rfl
  | succ target ih =>
      change machine.runConfigExact? ((target + 1) + 1)
        { state := Control.target nextHead
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend target rest) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_target_tick]
      simp only
      simpa [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc] using
        ih (MachineCodeSymbol.tick :: leftRev)
  done

theorem run_rewind
    (nextHead : Option Bool)
    (remainingRev crossed rest : Word MachineCodeSymbol)
    (hremaining : forall symbol : MachineCodeSymbol,
      List.Mem symbol remainingRev ->
      symbol = MachineCodeSymbol.tick ∨
        symbol = MachineCodeSymbol.done) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig nextHead remainingRev crossed rest) =
      some
        { state := Control.ready nextHead
          tape := SerializedShift.cursorTape [MachineCodeSymbol.header]
            (List.append remainingRev.reverse
              (List.append crossed
                (runtimeKeyCellSymbol nextHead :: rest))) } := by
  induction remainingRev generalizing crossed with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [step_rewind_blank]
      rfl
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1 + 1)
        (rewindConfig nextHead (current :: more) crossed rest) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_rewind_symbol nextHead current more crossed rest
        (hremaining current (List.Mem.head more))]
      simp only
      have hmore : forall symbol : MachineCodeSymbol,
          List.Mem symbol more ->
          symbol = MachineCodeSymbol.tick ∨
            symbol = MachineCodeSymbol.done := by
        intro symbol hmem
        exact hremaining symbol (List.Mem.tail current hmem)
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed) hmore
  done

theorem encodeNat_symbols
    (target : Nat) :
    forall symbol : MachineCodeSymbol,
      List.Mem symbol (MachineDescription.encodeNat target) ->
      symbol = MachineCodeSymbol.tick ∨
        symbol = MachineCodeSymbol.done := by
  induction target with
  | zero =>
      intro symbol hmem
      change List.Mem symbol [MachineCodeSymbol.done] at hmem
      have hdone : symbol = MachineCodeSymbol.done :=
        List.mem_singleton.mp hmem
      exact Or.inr hdone
  | succ target ih =>
      intro symbol hmem
      change List.Mem symbol
        (MachineCodeSymbol.tick :: MachineDescription.encodeNat target) at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inl rfl
      · exact ih symbol hmem
  done

theorem encodeNat_reverse_symbols
    (target : Nat) :
    forall symbol : MachineCodeSymbol,
      List.Mem symbol (MachineDescription.encodeNat target).reverse ->
      symbol = MachineCodeSymbol.tick ∨
        symbol = MachineCodeSymbol.done := by
  intro symbol hmem
  apply encodeNat_symbols target symbol
  exact List.mem_reverse.mp hmem
  done

theorem encodeNat_length
    (target : Nat) :
    (MachineDescription.encodeNat target).length = target + 1 := by
  induction target with
  | zero => rfl
  | succ target ih =>
      simp [MachineDescription.encodeNat, ih]
  done

theorem runConfigExact_trans
    {first second : Nat}
    {source middle targetConfig' :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some targetConfig') :
    machine.runConfigExact? (first + second) source = some targetConfig' := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hfirst)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hsecond)
  done

def runSteps (target : Nat) : Nat :=
  (target + 1) + 1 + ((target + 1) + 1)

theorem run_exact
    (nextHead : Option Bool)
    (target : Nat)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps target)
        (sourceConfig nextHead target rest) =
      some (targetConfig nextHead target rest) := by
  have htarget := run_target nextHead target []
    (MachineCodeSymbol.header :: rest)
  have hdelimiter :
      machine.runConfigExact? 1
          (delimiterConfig nextHead target rest) =
        some
          (rewindConfig nextHead
            (MachineDescription.encodeNat target).reverse [] rest) := by
    cases hrev : (MachineDescription.encodeNat target).reverse with
    | nil =>
        have hlength := congrArg List.length hrev
        simp [encodeNat_length target] at hlength
    | cons current more =>
        rw [TuringMachine.runConfigExact?]
        rw [show delimiterConfig nextHead target rest =
            { state := Control.delimiter nextHead
              tape := SerializedShift.cursorTape (current :: more)
                (MachineCodeSymbol.header :: rest) } by
          simp [delimiterConfig, hrev]]
        rw [step_delimiter]
        simp only [TuringMachine.runConfigExact?]
  have hrewind := run_rewind nextHead
    (MachineDescription.encodeNat target).reverse [] rest
    (encodeNat_reverse_symbols target)
  have hfirst := runConfigExact_trans
    (by simpa [sourceConfig, delimiterConfig] using htarget)
    hdelimiter
  have hall := runConfigExact_trans hfirst hrewind
  simpa [runSteps, sourceConfig, targetConfig, runtimeKeyBuilderKeyCode,
    runtimeKey_encodeCell_eq_singleton,
    MachineDescription.encodeNatAppend, encodeNat_length,
    List.append_assoc] using hall
  done

/-- Concrete nonempty-stack specialization: the restager consumes no table
cell and exposes exactly the next canonical single-key scan word. -/
theorem run_next_nonempty_copy
    (target : Nat)
    (nextHead : Option Bool)
    (first : TransitionDescription)
    (transitions : List TransitionDescription)
    (copies : Nat)
    (updatedTape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps target)
        (sourceConfig nextHead target
          (MachineDescription.encodeTransitionsAppend
            (first :: transitions)
            (MachineCodeSymbol.header ::
              List.append (tableStack (first :: transitions) copies)
                (contextTail updatedTape haltState callerSuffix)))) =
      some
        (targetConfig nextHead target
          (MachineDescription.encodeTransitionsAppend
            (first :: transitions)
            (MachineCodeSymbol.header ::
              List.append (tableStack (first :: transitions) copies)
                (contextTail updatedTape haltState callerSuffix)))) := by
  exact run_exact nextHead target _
  done

end NextCopyRestager

/-!
**Stack architecture.** The initializer converts a nonempty raw table into a
fuel-indexed stack while preserving parsed input and halt metadata. Nonempty
tables start with transition and contain no header, so the double header
identifies only the stack/context boundary. The empty-table branch is separate.
The serialized halt state and both unbounded tape contexts stay on tape
throughout execution.
-/


end FiniteRecognizer.Interpreter.LoopRestagingAudit

end Computability
end FoC

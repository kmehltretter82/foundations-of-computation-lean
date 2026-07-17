import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Closeout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextIngress

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.RuntimeEncodedList
open FiniteRecognizer.Interpreter.BooleanContextLocator
open FiniteRecognizer.Interpreter.BooleanContextRawTail
open FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound

/-- The three tokens installed after the parser's preserved table marker:
the empty left-list count, the empty right-list count, and the raw-tail
marker. -/
def contextBuffer : InsertBlock.Buffer where
  word := [MachineCodeSymbol.done, MachineCodeSymbol.done,
    MachineCodeSymbol.header]
  length_le := by simp

theorem contextBuffer_nonempty : contextBuffer.word ≠ [] := by
  simp [contextBuffer]

namespace Machine

inductive Control where
  | enter (saved : Option MachineCodeSymbol)
  | counter (saved : Option MachineCodeSymbol)
  | rowsLeft (saved : Option MachineCodeSymbol)
  | rowsRight (saved : Option MachineCodeSymbol)
  | tableRight (saved : Option MachineCodeSymbol)
  | insert (saved : Option MachineCodeSymbol)
      (inner : InsertRestagedMachine.Control)
  | insertBounce (saved : Option MachineCodeSymbol)
  | locate (saved : Option MachineCodeSymbol)
      (inner : FiniteRecognizer.Interpreter.BooleanContextLocator.Control)
  | locateBounce (saved : Option MachineCodeSymbol)
  | ready (saved : Option MachineCodeSymbol)
deriving DecidableEq

namespace Control

def savedOptions : List (Option MachineCodeSymbol) :=
  none :: MachineCodeSymbol.finite.elems.map some

theorem savedOptions_complete
    (saved : Option MachineCodeSymbol) : saved ∈ savedOptions := by
  cases saved with
  | none => simp [savedOptions]
  | some symbol =>
      simp [savedOptions, MachineCodeSymbol.finite.complete symbol]

def savedControls
    (f : Option MachineCodeSymbol -> Control) : List Control :=
  savedOptions.map f

def savedInnerControls
    {inner : Type}
    (innerElems : List inner)
    (f : Option MachineCodeSymbol -> inner -> Control) : List Control :=
  savedOptions.flatMap fun saved => innerElems.map (f saved)

theorem savedControls_complete
    (f : Option MachineCodeSymbol -> Control)
    (saved : Option MachineCodeSymbol) :
    f saved ∈ savedControls f := by
  exact List.mem_map.mpr ⟨saved, savedOptions_complete saved, rfl⟩

theorem savedInnerControls_complete
    {inner : Type}
    (innerElems : List inner)
    (hinner : forall value : inner, value ∈ innerElems)
    (f : Option MachineCodeSymbol -> inner -> Control)
    (saved : Option MachineCodeSymbol) (value : inner) :
    f saved value ∈ savedInnerControls innerElems f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, savedOptions_complete saved, ?_⟩
  exact List.mem_map.mpr ⟨value, hinner value, rfl⟩

def elems : List Control :=
  savedControls Control.enter ++
    savedControls Control.counter ++
    savedControls Control.rowsLeft ++
    savedControls Control.rowsRight ++
    savedControls Control.tableRight ++
    savedInnerControls InsertRestagedMachine.Control.finite.elems
      Control.insert ++
    savedControls Control.insertBounce ++
    savedInnerControls FiniteRecognizer.Interpreter.BooleanContextLocator.Control.finite.elems
      Control.locate ++
    savedControls Control.locateBounce ++
    savedControls Control.ready

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | enter saved =>
        have h := savedControls_complete Control.enter saved
        simp [elems, h]
    | counter saved =>
        have h := savedControls_complete Control.counter saved
        simp [elems, h]
    | rowsLeft saved =>
        have h := savedControls_complete Control.rowsLeft saved
        simp [elems, h]
    | rowsRight saved =>
        have h := savedControls_complete Control.rowsRight saved
        simp [elems, h]
    | tableRight saved =>
        have h := savedControls_complete Control.tableRight saved
        simp [elems, h]
    | insert saved inner =>
        have h := savedInnerControls_complete
          InsertRestagedMachine.Control.finite.elems
          InsertRestagedMachine.Control.finite.complete
          Control.insert saved inner
        simp [elems, h]
    | insertBounce saved =>
        have h := savedControls_complete Control.insertBounce saved
        simp [elems, h]
    | locate saved inner =>
        have h := savedInnerControls_complete
          FiniteRecognizer.Interpreter.BooleanContextLocator.Control.finite.elems
          FiniteRecognizer.Interpreter.BooleanContextLocator.Control.finite.complete
          Control.locate saved inner
        simp [elems, h]
    | locateBounce saved =>
        have h := savedControls_complete Control.locateBounce saved
        simp [elems, h]
    | ready saved =>
        have h := savedControls_complete Control.ready saved
        simp [elems, h]

end Control

def mapInsertAction
    (saved : Option MachineCodeSymbol) :
    (Option MachineCodeSymbol × Direction ×
        InsertRestagedMachine.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, target) =>
      (write, direction, .insert saved target)

def mapLocatorAction
    (saved : Option MachineCodeSymbol) :
    (Option MachineCodeSymbol × Direction ×
        FiniteRecognizer.Interpreter.BooleanContextLocator.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, target) =>
      (write, direction, .locate saved target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter saved, read =>
      some (read, Direction.left, .counter saved)
  | .counter saved, read =>
      some (read, Direction.left, .rowsLeft saved)
  | .rowsLeft saved, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.left, .rowsLeft saved)
  | .rowsLeft saved, none =>
      some (some MachineCodeSymbol.blank, Direction.right, .rowsRight saved)
  | .rowsRight saved, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .rowsRight saved)
  | .rowsRight saved, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .tableRight saved)
  | .tableRight saved, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right,
        .insert saved (InsertRestagedMachine.machine contextBuffer).start)
  | .tableRight saved, some symbol =>
      some (some symbol, Direction.right, .tableRight saved)
  | .insert saved (.rewind .gate), read =>
      some (read, Direction.left, .insertBounce saved)
  | .insert saved inner, read =>
      Option.map (mapInsertAction saved)
        (InsertRestagedMachine.transition inner read)
  | .insertBounce saved, read =>
      some (read, Direction.right,
        .locate saved FiniteRecognizer.Interpreter.BooleanContextLocator.Control.fuel)
  | .locate saved .ready, read =>
      some (read, Direction.left, .locateBounce saved)
  | .locate saved inner, read =>
      Option.map (mapLocatorAction saved)
        (FiniteRecognizer.Interpreter.BooleanContextLocator.transition inner read)
  | .locateBounce saved, read =>
      some (read, Direction.right, .ready saved)
  | .ready _, _ => none
  | _, _ => none

def entry (saved : Option MachineCodeSymbol) : Control := .enter saved

def machine : TuringMachine MachineCodeSymbol Control where
  start := entry none
  halt := .ready none
  transition := transition
  statesFinite := Control.finite

def insertConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .insert saved config.state, tape := config.tape }

def locatorConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .locate saved config.state, tape := config.tape }

theorem insert_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control)
    (hstep : (InsertRestagedMachine.machine contextBuffer).stepConfig
      source = some target) :
    machine.stepConfig (insertConfig saved source) =
      some (insertConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [InsertRestagedMachine.machine] at hstep
      cases htransition :
          InsertRestagedMachine.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠ InsertRestagedMachine.Control.rewind
              RewindWord.Control.gate := by
            intro heq
            subst inner
            simp [InsertRestagedMachine.transition,
              RewindWord.transition] at htransition
          simp [machine, transition, insertConfig, htransition,
            hnot, mapInsertAction]

theorem insert_run_of_some
    (saved : Option MachineCodeSymbol) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        InsertRestagedMachine.Control),
      (InsertRestagedMachine.machine contextBuffer).runConfigExact?
          steps source = some target ->
        machine.runConfigExact? steps (insertConfig saved source) =
          some (insertConfig saved target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg (insertConfig saved) (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (InsertRestagedMachine.machine contextBuffer).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [insert_step_of_some saved source next hstep]
          simp only
          exact ih next target hrun

theorem locator_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control)
    (hstep : FiniteRecognizer.Interpreter.BooleanContextLocator.machine.stepConfig source =
      some target) :
    machine.stepConfig (locatorConfig saved source) =
      some (locatorConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.BooleanContextLocator.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.BooleanContextLocator.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠ FiniteRecognizer.Interpreter.BooleanContextLocator.Control.ready := by
            intro heq
            subst inner
            simp [FiniteRecognizer.Interpreter.BooleanContextLocator.transition] at htransition
          simp [machine, transition, locatorConfig, htransition,
            hnot, mapLocatorAction]

theorem locator_computes_lift
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextLocator.machine source target) :
    TuringMachine.Computes machine
      (locatorConfig saved source) (locatorConfig saved target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (locator_step_of_some saved _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

def parserSourceConfig
    (saved : Option MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (extraRows : Nat)
    (tableHead : MachineCodeSymbol)
    (tableTail raw : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := entry saved
    tape :=
      { left :=
          some MachineCodeSymbol.done ::
            List.append
              (List.replicate (extraRows + 1)
                (some MachineCodeSymbol.blank))
              (none :: baseLeftRev.map some)
        head := some tableHead
        right :=
          List.append (tableTail.map some)
            (some MachineCodeSymbol.header :: raw.map some) } }

def rowsLeftConfig
    (saved : Option MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (remaining : Nat)
    (rightWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rowsLeft saved
    tape :=
      { left :=
          List.append
            (List.replicate remaining (some MachineCodeSymbol.blank))
            (none :: baseLeftRev.map some)
        head := some MachineCodeSymbol.blank
        right := rightWord.map some } }

theorem parser_prelude_run_exact
    (saved : Option MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (extraRows : Nat)
    (tableHead : MachineCodeSymbol)
    (tableTail raw : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (parserSourceConfig saved baseLeftRev extraRows tableHead
          tableTail raw) =
      some
        (rowsLeftConfig saved baseLeftRev extraRows
          (MachineCodeSymbol.done :: tableHead ::
            List.append tableTail
              (MachineCodeSymbol.header :: raw))) := by
  cases extraRows <;> cases baseLeftRev <;> cases tableTail <;>
    cases raw <;>
      simp [parserSourceConfig, rowsLeftConfig, entry, machine, transition,
        TuringMachine.runConfigExact?, TuringMachine.stepConfig,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.replicate_succ, List.map_append, List.append_assoc]

theorem rowsLeft_zero_run_exact
    (saved : Option MachineCodeSymbol)
    (baseLeftRev rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (rowsLeftConfig saved baseLeftRev 0 rightWord) =
      some
        { state := .rowsRight saved
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.blank :: baseLeftRev)
            (MachineCodeSymbol.blank :: rightWord) } := by
  cases baseLeftRev <;> cases rightWord <;> rfl

theorem rowsLeft_succ_step
    (saved : Option MachineCodeSymbol)
    (baseLeftRev rightWord : Word MachineCodeSymbol)
    (remaining : Nat) :
    machine.stepConfig
        (rowsLeftConfig saved baseLeftRev (remaining + 1) rightWord) =
      some
        (rowsLeftConfig saved baseLeftRev remaining
          (MachineCodeSymbol.blank :: rightWord)) := by
  cases remaining <;> cases baseLeftRev <;> cases rightWord <;> rfl

theorem rowsLeft_computes
    (saved : Option MachineCodeSymbol)
    (baseLeftRev rightWord : Word MachineCodeSymbol)
    (remaining : Nat) :
    TuringMachine.Computes machine
      (rowsLeftConfig saved baseLeftRev remaining rightWord)
      { state := .rowsRight saved
        tape := SerializedShift.cursorTape
          (MachineCodeSymbol.blank :: baseLeftRev)
          (List.append
            (List.replicate (remaining + 1) MachineCodeSymbol.blank)
            rightWord) } := by
  induction remaining generalizing rightWord with
  | zero =>
      exact TuringMachine.computesIn_to_computes
        (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
          (by
            simpa using rowsLeft_zero_run_exact saved baseLeftRev rightWord))
  | succ remaining ih =>
      have hcommute :=
        list_replicate_append_cons_eq_cons_append
          MachineCodeSymbol.blank remaining rightWord
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (rowsLeft_succ_step saved baseLeftRev rightWord remaining))
        (by
          simpa [List.replicate_succ, hcommute,
            List.append_assoc] using
            ih (MachineCodeSymbol.blank :: rightWord))

def rowsRightConfig
    (saved : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rowsRight saved
    tape := SerializedShift.cursorTape leftRev rest }

def tableRightConfig
    (saved : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .tableRight saved
    tape := SerializedShift.cursorTape leftRev rest }

theorem rowsRight_blank_step
    (saved : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (rowsRightConfig saved leftRev
          (MachineCodeSymbol.blank :: rest)) =
      some
        (rowsRightConfig saved
          (MachineCodeSymbol.blank :: leftRev) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem rowsRight_done_step
    (saved : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (rowsRightConfig saved leftRev
          (MachineCodeSymbol.done :: rest)) =
      some
        (tableRightConfig saved
          (MachineCodeSymbol.done :: leftRev) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem rowsRight_computes
    (saved : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol)
    (count : Nat) :
    TuringMachine.Computes machine
      (rowsRightConfig saved leftRev
        (List.append
          (List.replicate count MachineCodeSymbol.blank)
          (MachineCodeSymbol.done :: rest)))
      (tableRightConfig saved
        (MachineCodeSymbol.done ::
          List.append
            (List.replicate count MachineCodeSymbol.blank) leftRev)
        rest) := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (rowsRight_done_step saved leftRev rest))
        (TuringMachine.Computes.refl _)
  | succ count ih =>
      have hcommute :=
        list_replicate_append_cons_eq_cons_append
          MachineCodeSymbol.blank count leftRev
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (rowsRight_blank_step saved leftRev
                (List.append
                  (List.replicate count MachineCodeSymbol.blank)
                  (MachineCodeSymbol.done :: rest))))
        (by
          simpa [List.replicate_succ, hcommute,
            List.append_assoc] using
            ih (MachineCodeSymbol.blank :: leftRev))

theorem tableRight_symbol_step
    (saved : Option MachineCodeSymbol)
    (leftRev rest : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (tableRightConfig saved leftRev (symbol :: rest)) =
      some
        (tableRightConfig saved (symbol :: leftRev) rest) := by
  cases symbol <;> cases leftRev <;> cases rest <;>
    simp_all [machine, transition, tableRightConfig,
      TuringMachine.stepConfig, SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem tableRight_header_step
    (saved : Option MachineCodeSymbol)
    (leftRev raw : Word MachineCodeSymbol) :
    machine.stepConfig
        (tableRightConfig saved leftRev
          (MachineCodeSymbol.header :: raw)) =
      some
        (insertConfig saved
          (InsertRestagedMachine.editConfig
            (InsertBlock.config contextBuffer
              (MachineCodeSymbol.header :: leftRev) raw))) := by
  cases leftRev <;> cases raw <;> rfl

theorem tableRight_computes
    (saved : Option MachineCodeSymbol)
    (leftRev table raw : Word MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table) :
    TuringMachine.Computes machine
      (tableRightConfig saved leftRev
        (List.append table (MachineCodeSymbol.header :: raw)))
      (insertConfig saved
        (InsertRestagedMachine.editConfig
          (InsertBlock.config contextBuffer
            (MachineCodeSymbol.header ::
              List.append table.reverse leftRev) raw))) := by
  induction table generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (tableRight_header_step saved leftRev raw))
        (TuringMachine.Computes.refl _)
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ MachineCodeSymbol.header :=
        hnoHeader symbol (List.Mem.head rest)
      have hrest : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader rest := by
        intro current hmem
        exact hnoHeader current (List.Mem.tail symbol hmem)
      exact TuringMachine.Computes.step
        (by
          simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
            (tableRight_symbol_step saved leftRev
              (List.append rest (MachineCodeSymbol.header :: raw))
              symbol hsymbol))
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (symbol :: leftRev) hrest)

def setupLeftRev
    (baseLeftRev : Word MachineCodeSymbol)
    (rowCount : Nat)
    (table : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append table.reverse
      (MachineCodeSymbol.done ::
        List.append
          (List.replicate rowCount MachineCodeSymbol.blank)
          (MachineCodeSymbol.blank :: baseLeftRev))

def setupWord
    (baseLeftRev : Word MachineCodeSymbol)
    (rowCount : Nat)
    (table raw : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  PhysicalBranch.insertOutput contextBuffer
    (setupLeftRev baseLeftRev rowCount table) raw

theorem parser_setup_computes
    (saved : Option MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (extraRows : Nat)
    (tableHead : MachineCodeSymbol)
    (tableTail raw : Word MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader
      (tableHead :: tableTail)) :
    TuringMachine.Computes machine
      (parserSourceConfig saved baseLeftRev extraRows tableHead
        tableTail raw)
      (insertConfig saved
        (InsertRestagedMachine.editConfig
          (InsertBlock.config contextBuffer
            (setupLeftRev baseLeftRev (extraRows + 1)
              (tableHead :: tableTail)) raw))) := by
  have hprelude := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (parser_prelude_run_exact saved baseLeftRev extraRows tableHead
        tableTail raw))
  have hleft := rowsLeft_computes saved baseLeftRev
    (MachineCodeSymbol.done :: tableHead ::
      List.append tableTail (MachineCodeSymbol.header :: raw))
    extraRows
  have hright := rowsRight_computes saved
    (MachineCodeSymbol.blank :: baseLeftRev)
    (List.append (tableHead :: tableTail)
      (MachineCodeSymbol.header :: raw))
    (extraRows + 1)
  have htable := tableRight_computes saved
    (MachineCodeSymbol.done ::
      List.append
        (List.replicate (extraRows + 1) MachineCodeSymbol.blank)
        (MachineCodeSymbol.blank :: baseLeftRev))
    (tableHead :: tableTail) raw hnoHeader
  have hrun := TuringMachine.computes_trans hprelude hleft
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [rowsRightConfig] using hright)
  have hrun := TuringMachine.computes_trans hrun htable
  simpa [setupLeftRev, List.append_assoc] using hrun

theorem setup_insert_computes
    (saved : Option MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (rowCount : Nat)
    (table raw : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (insertConfig saved
        (InsertRestagedMachine.editConfig
          (InsertBlock.config contextBuffer
            (setupLeftRev baseLeftRev rowCount table) raw)))
      (insertConfig saved
        (InsertRestagedMachine.rewindConfig
          (RewindWord.gateConfig
            (setupWord baseLeftRev rowCount table raw) 0))) := by
  have hinner := InsertRestagedMachine.run_exact contextBuffer
    (setupLeftRev baseLeftRev rowCount table) raw contextBuffer_nonempty
  have hlift := insert_run_of_some saved _ _ _ hinner
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (by simpa [setupWord] using hlift))

theorem insert_to_locator_run_exact
    (saved : Option MachineCodeSymbol)
    (word : Word MachineCodeSymbol)
    (hword : word ≠ []) :
    machine.runConfigExact? 2
        { state := .insert saved (.rewind .gate)
          tape := RewindWord.gateTape word 0 } =
      some
        { state := .locate saved .fuel
          tape := RewindWord.gateTape word 0 } := by
  cases word with
  | nil => contradiction
  | cons first rest => cases rest <;> rfl

theorem setupWord_ne_nil
    (baseLeftRev : Word MachineCodeSymbol)
    (rowCount : Nat)
    (table raw : Word MachineCodeSymbol) :
    setupWord baseLeftRev rowCount table raw ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [setupWord, PhysicalBranch.insertOutput, setupLeftRev] at hlength

theorem setup_to_locator_computes
    (saved : Option MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (rowCount : Nat)
    (table raw : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (insertConfig saved
        (InsertRestagedMachine.editConfig
          (InsertBlock.config contextBuffer
            (setupLeftRev baseLeftRev rowCount table) raw)))
      { state := .locate saved .fuel
        tape := RewindWord.gateTape
          (setupWord baseLeftRev rowCount table raw) 0 } := by
  have hinsert := setup_insert_computes saved baseLeftRev rowCount table raw
  have hbounce := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (insert_to_locator_run_exact saved
        (setupWord baseLeftRev rowCount table raw)
        (setupWord_ne_nil baseLeftRev rowCount table raw)))
  exact TuringMachine.computes_trans hinsert (by
    simpa [insertConfig, InsertRestagedMachine.rewindConfig,
      RewindWord.gateConfig] using hbounce)

theorem setupWord_eq_locatorWord
    (D : MachineDescription)
    (fuel : Nat)
    (table raw : Word MachineCodeSymbol) :
    setupWord (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
        D.transitions.length table raw =
      FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.layoutWord
        fuel D.stateCount D.start D.halt D.transitions.length
        table [] raw := by
  simp [setupWord, setupLeftRev, PhysicalBranch.insertOutput,
    contextBuffer,
    FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.layoutWord,
    FiniteRecognizer.Interpreter.BooleanContextLocator.locatorWord,
    FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix,
    FiniteRecognizer.Interpreter.BooleanContextLocator.parsedMetadataAppend,
    FiniteRecognizer.Interpreter.BooleanContextLocator.parserTailBeforeRightCount,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterStartLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterStateLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHeaderLeftRev,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat,
    MachineDescription.encodeCellsAppend,
    List.reverse_append, List.append_assoc]

theorem marked_source_eq_parserSourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (tableHead : MachineCodeSymbol)
    (tableTail : Word MachineCodeSymbol)
    (htable : MachineDescription.encodeTransitions (first :: rest) =
      tableHead :: tableTail) :
    { state := entry (transitionListParserSavedHead input)
      tape := markedParserMaterializerSourceTape baseLeftRev
        first rest input } =
      parserSourceConfig (transitionListParserSavedHead input)
        baseLeftRev rest.length tableHead tableTail input.tail := by
  cases input with
  | nil =>
      simp [markedParserMaterializerSourceTape,
        appendParsedLeftContext, parsedTransitionHaltConfig,
        parsedTableLeftRev, transitionListParserOptionTape,
        transitionListParserMarkedTail, transitionListParserSavedHead,
        parserSourceConfig, htable, List.replicate_succ,
        List.map_append, List.append_assoc]
  | cons inputHead inputTail =>
      simp [markedParserMaterializerSourceTape,
        appendParsedLeftContext, parsedTransitionHaltConfig,
        parsedTableLeftRev, transitionListParserOptionTape,
        transitionListParserMarkedTail, transitionListParserSavedHead,
        parserSourceConfig, htable, List.replicate_succ,
        List.map_append, List.append_assoc]

def locatorBounceTape (tape : Tape MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.move Direction.right (Tape.move Direction.left tape)

theorem locatorBounceTape_equiv (tape : Tape MachineCodeSymbol) :
    Tape.Equiv (locatorBounceTape tape) tape := by
  cases tape with
  | mk left head right =>
      simp [locatorBounceTape, Tape.Equiv, Tape.move,
        Tape.moveLeft, Tape.moveRight]
      cases left <;> simp [Tape.dropTrailingNone]

theorem locator_to_ready_run_exact
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := .locate saved .ready, tape := tape } =
      some
        { state := .ready saved, tape := locatorBounceTape tape } := by
  cases tape
  rfl

theorem locator_to_ready_computes
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .locate saved .ready, tape := tape }
      { state := .ready saved, tape := locatorBounceTape tape } := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (locator_to_ready_run_exact saved tape))

theorem locator_from_setup_computes
    (saved : Option MachineCodeSymbol)
    (D : MachineDescription)
    (fuel : Nat)
    (table raw : Word MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .locate saved .fuel
          tape := RewindWord.gateTape
            (setupWord
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
              D.transitions.length table raw) 0 }
        { state := .ready saved, tape := targetTape } ∧
      Tape.Equiv
        (RawTailPop.sourceConfig
          (FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
            fuel D.stateCount D.start D.halt D.transitions.length table)
          [] raw).tape
        targetTape := by
  let canonicalSource :=
    FiniteRecognizer.Interpreter.BooleanContextLocator.sourceConfig
      fuel D.stateCount D.start D.halt D.transitions.length table 0
      (MachineCodeSymbol.header :: raw)
  let canonicalTarget :=
    FiniteRecognizer.Interpreter.BooleanContextLocator.targetConfig
      fuel D.stateCount D.start D.halt D.transitions.length table 0
      (MachineCodeSymbol.header :: raw)
  have hcanonical : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextLocator.machine canonicalSource
      canonicalTarget := by
    exact FiniteRecognizer.Interpreter.BooleanContextLocator.computes_to_right_count
      fuel D.stateCount D.start D.halt D.transitions.length table 0
      (MachineCodeSymbol.header :: raw) hnoHeader
  have hsource : Tape.Equiv canonicalSource.tape
      (RewindWord.gateTape
        (setupWord
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
          D.transitions.length table raw) 0) := by
    rw [show canonicalSource =
        FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.locatorSource
          fuel D.stateCount D.start D.halt D.transitions.length table [] raw
      by rfl]
    rw [FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.locatorSource_tape_eq_input]
    rw [← setupWord_eq_locatorWord D fuel table raw]
    exact Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (setupWord
          (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
          D.transitions.length table raw) 0)
  rcases TuringMachine.computes_to_computesIn hcanonical with
    ⟨steps, hcanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalIn hsource with
    ⟨actualTarget, hactualRun, hactualState, hactualTape⟩
  rcases actualTarget with ⟨actualState, actualTape⟩
  simp only at hactualState
  subst actualState
  have hinner : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextLocator.machine
        { state := FiniteRecognizer.Interpreter.BooleanContextLocator.Control.fuel
          tape := RewindWord.gateTape
            (setupWord
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D fuel)
              D.transitions.length table raw) 0 }
        { state := FiniteRecognizer.Interpreter.BooleanContextLocator.Control.ready
          tape := actualTape } := by
    simpa [canonicalSource, canonicalTarget,
      FiniteRecognizer.Interpreter.BooleanContextLocator.sourceConfig,
      FiniteRecognizer.Interpreter.BooleanContextLocator.targetConfig,
      FiniteRecognizer.Interpreter.BooleanContextLocator.config] using
      TuringMachine.computesIn_to_computes hactualRun
  have hlift := locator_computes_lift saved hinner
  have hbounce := locator_to_ready_computes saved actualTape
  refine ⟨locatorBounceTape actualTape,
    TuringMachine.computes_trans hlift hbounce, ?_⟩
  have htarget : Tape.Equiv
      (RawTailPop.sourceConfig
        (FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
          fuel D.stateCount D.start D.halt D.transitions.length table)
        [] raw).tape
      actualTape := by
    simpa [canonicalTarget,
      FiniteRecognizer.Interpreter.BooleanContextLocator.targetConfig,
      FiniteRecognizer.Interpreter.BooleanContextLocator.config,
      FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev,
      RawTailPop.sourceConfig, PayloadLocator.sourceConfig,
      RawTailPop.locateConfig, MachineDescription.encodeCellsAppend] using
        hactualTape
  exact Tape.Equiv.trans htarget
    (Tape.Equiv.symm (locatorBounceTape_equiv actualTape))

theorem parsed_ingress_computes
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := entry (transitionListParserSavedHead input)
          tape := markedParserMaterializerSourceTape
            (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
              (remainingFuel + 1)) first rest input }
        { state := .ready (transitionListParserSavedHead input)
          tape := targetTape } ∧
      Tape.Equiv
        (RawTailPop.sourceConfig
          (FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
            (remainingFuel + 1) D.stateCount D.start D.halt
            D.transitions.length
            (MachineDescription.encodeTransitions (first :: rest)))
          [] input.tail).tape
        targetTape := by
  have htableNonempty :
      MachineDescription.encodeTransitions (first :: rest) ≠ [] := by
    simp [MachineDescription.encodeTransitions,
      MachineDescription.encodeTransitionsAppend,
      MachineDescription.encodeTransitionAppend]
  cases htable : MachineDescription.encodeTransitions (first :: rest) with
  | nil => contradiction
  | cons tableHead tableTail =>
      have hnoHeaderRaw :=
        transitionListParser_encodeTransitionsAppend_noHeader
          (first :: rest) (suffix := []) (by
            intro symbol hmem
            simp at hmem)
      have hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader
          (tableHead :: tableTail) := by
        change transitionListParserNoHeader
          (MachineDescription.encodeTransitions (first :: rest)) at hnoHeaderRaw
        rw [htable] at hnoHeaderRaw
        exact hnoHeaderRaw
      have hsource := marked_source_eq_parserSourceConfig
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1)) first rest input tableHead tableTail htable
      have hsetup := parser_setup_computes
        (transitionListParserSavedHead input)
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1)) rest.length tableHead tableTail input.tail
        hnoHeader
      have hinsert := setup_to_locator_computes
        (transitionListParserSavedHead input)
        (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
          (remainingFuel + 1)) (rest.length + 1)
        (tableHead :: tableTail) input.tail
      have hprefix : TuringMachine.Computes machine
          { state := entry (transitionListParserSavedHead input)
            tape := markedParserMaterializerSourceTape
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
                (remainingFuel + 1)) first rest input }
          { state := .locate (transitionListParserSavedHead input) .fuel
            tape := RewindWord.gateTape
              (setupWord
                (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
                  (remainingFuel + 1))
                (rest.length + 1) (tableHead :: tableTail) input.tail) 0 } := by
        rw [hsource]
        exact TuringMachine.computes_trans hsetup hinsert
      have hlength : D.transitions.length = rest.length + 1 := by
        rw [htransitions]
        simp
      rcases locator_from_setup_computes
          (transitionListParserSavedHead input) D (remainingFuel + 1)
          (tableHead :: tableTail) input.tail hnoHeader with
        ⟨targetTape, hlocator, htarget⟩
      have hprefix' : TuringMachine.Computes machine
          { state := entry (transitionListParserSavedHead input)
            tape := markedParserMaterializerSourceTape
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
                (remainingFuel + 1)) first rest input }
          { state := .locate (transitionListParserSavedHead input) .fuel
            tape := RewindWord.gateTape
              (setupWord
                (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
                  (remainingFuel + 1))
                D.transitions.length (tableHead :: tableTail) input.tail) 0 } := by
        simpa [hlength] using hprefix
      refine ⟨targetTape,
        TuringMachine.computes_trans hprefix' hlocator, ?_⟩
      simpa [htable] using htarget


end Machine

end FiniteRecognizer.Interpreter.BooleanContextIngress

end Computability
end FoC

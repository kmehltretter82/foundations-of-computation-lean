import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Halt

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter

open FiniteRecognizer ExactFuel StrictProbe
open FiniteRecognizer.Interpreter.InitializerPersistentCopy

namespace Machine

inductive Control where
  | fuel
  | needHeader
  | stateCount
  | startState
  | haltState
  | oldSeparator
  | rowBlanks
  | table
  | shift (carried : MachineCodeSymbol)
  | atEnd
  | rewindSuffix
  | bounce
  | ready
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.fuel, .needHeader, .stateCount, .startState, .haltState,
    .oldSeparator, .rowBlanks, .table, .atEnd, .rewindSuffix,
    .bounce, .ready] ++ MachineCodeSymbol.finite.elems.map shift

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | shift carried =>
        simp [elems, MachineCodeSymbol.finite.complete carried]
    | fuel => simp [elems]
    | needHeader => simp [elems]
    | stateCount => simp [elems]
    | startState => simp [elems]
    | haltState => simp [elems]
    | oldSeparator => simp [elems]
    | rowBlanks => simp [elems]
    | table => simp [elems]
    | atEnd => simp [elems]
    | rewindSuffix => simp [elems]
    | bounce => simp [elems]
    | ready => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .fuel, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .needHeader)
  | .needHeader, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .stateCount)
  | .stateCount, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .stateCount)
  | .stateCount, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .startState)
  | .startState, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .startState)
  | .startState, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .haltState)
  | .haltState, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .haltState)
  | .haltState, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .oldSeparator)
  | .oldSeparator, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .rowBlanks)
  | .rowBlanks, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .rowBlanks)
  | .rowBlanks, some MachineCodeSymbol.done =>
      some (none, Direction.right, .table)
  | .table, some MachineCodeSymbol.header =>
      some (none, Direction.right, .shift MachineCodeSymbol.header)
  | .table, some symbol =>
      some (some symbol, Direction.right, .table)
  | .shift carried, some current =>
      some (some carried, Direction.right, .shift current)
  | .shift carried, none =>
      some (some carried, Direction.right, .atEnd)
  | .atEnd, none => some (none, Direction.left, .rewindSuffix)
  | .rewindSuffix, some symbol =>
      some (some symbol, Direction.left, .rewindSuffix)
  | .rewindSuffix, none => some (none, Direction.right, .bounce)
  | .bounce, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.left, .ready)
  | .ready, _ => none
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .fuel
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def config
    (state : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state
    tape := SerializedShift.cursorTape leftRev rest }

theorem cursor_step
    (state next : Control)
    (leftRev rest : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (write : MachineCodeSymbol)
    (htransition : transition state (some symbol) =
      some (some write, Direction.right, next)) :
    TuringMachine.Step machine
      (config state leftRev (symbol :: rest))
      (config next (write :: leftRev) rest) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases rest <;>
    simp [TuringMachine.stepConfig, machine, config,
      SerializedShift.cursorTape, htransition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]

theorem scanUnary_computes
    (state next : Control)
    (htick : transition state (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, state))
    (hdone : transition state (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, next))
    (count : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config state leftRev
        (MachineDescription.encodeNatAppend count suffix))
      (config next
        (List.append (MachineDescription.encodeNat count).reverse leftRev)
        suffix) := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (cursor_step state next leftRev suffix MachineCodeSymbol.done
          MachineCodeSymbol.done hdone)
        (TuringMachine.Computes.refl _)
  | succ count ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using
            cursor_step state state leftRev
              (MachineDescription.encodeNatAppend count suffix)
              MachineCodeSymbol.tick MachineCodeSymbol.tick htick)
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat, List.append_assoc] using
            ih (MachineCodeSymbol.tick :: leftRev))

def metadataWithHalt
    (fuel stateCount start halt : Nat) : Word MachineCodeSymbol :=
  List.append
    (FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.metadataPrefix
      fuel stateCount start)
    (MachineDescription.encodeNat halt)

def baseLeftRev
    (fuel stateCount start halt rowCount : Nat) :
    Word MachineCodeSymbol :=
  List.append (List.replicate rowCount MachineCodeSymbol.blank)
    (MachineCodeSymbol.blank ::
      (metadataWithHalt fuel stateCount start halt).reverse)

def sourceWord
    (fuel stateCount start halt rowCount : Nat)
    (table suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (metadataWithHalt fuel stateCount start halt)
    (MachineCodeSymbol.blank ::
      List.append (List.replicate rowCount MachineCodeSymbol.blank)
        (MachineCodeSymbol.done :: List.append table suffix))

def sourceConfig
    (fuel stateCount start halt rowCount : Nat)
    (table suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .fuel
    tape := Tape.input
      (sourceWord fuel stateCount start halt rowCount table suffix) }

def targetConfig
    (fuel stateCount start halt rowCount : Nat)
    (table suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready
    tape := PersistentMasterCopier.sourceTape
      (baseLeftRev fuel stateCount start halt rowCount) table suffix }

theorem metadata_scan_computes
    (fuel stateCount start halt : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .fuel []
        (List.append (metadataWithHalt fuel stateCount start halt) suffix))
      (config .oldSeparator
        (metadataWithHalt fuel stateCount start halt).reverse suffix) := by
  let afterFuel : Word MachineCodeSymbol :=
    (MachineDescription.encodeNat fuel).reverse
  let afterHeader : Word MachineCodeSymbol :=
    MachineCodeSymbol.header :: afterFuel
  let afterState : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat stateCount).reverse
      afterHeader
  let afterStart : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat start).reverse afterState
  have hfuel := scanUnary_computes .fuel .needHeader rfl rfl fuel []
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend stateCount
        (MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt suffix)))
  have hheader : TuringMachine.Computes machine
      (config .needHeader afterFuel
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix))))
      (config .stateCount afterHeader
        (MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt suffix)))) := by
    exact TuringMachine.Computes.step
      (cursor_step .needHeader .stateCount afterFuel _
        MachineCodeSymbol.header MachineCodeSymbol.header rfl)
      (TuringMachine.Computes.refl _)
  have hstate := scanUnary_computes .stateCount .startState rfl rfl
    stateCount afterHeader
    (MachineDescription.encodeNatAppend start
      (MachineDescription.encodeNatAppend halt suffix))
  have hstart := scanUnary_computes .startState .haltState rfl rfl
    start afterState (MachineDescription.encodeNatAppend halt suffix)
  have hhalt := scanUnary_computes .haltState .oldSeparator rfl rfl
    halt afterStart suffix
  have hrun := TuringMachine.computes_trans hfuel (by
    simpa [afterFuel] using hheader)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterHeader] using hstate)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterState] using hstart)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterStart, afterState] using hhalt)
  simpa [metadataWithHalt,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.metadataPrefix,
    MachineDescription.encodeNatAppend, List.reverse_append,
    afterFuel, afterHeader, afterState, afterStart,
    List.append_assoc] using hrun

theorem oldSeparator_step
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .oldSeparator leftRev
          (MachineCodeSymbol.blank :: rest)) =
      some
        (config .rowBlanks
          (MachineCodeSymbol.blank :: leftRev) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem rowBlank_step
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .rowBlanks leftRev
          (MachineCodeSymbol.blank :: rest)) =
      some
        (config .rowBlanks
          (MachineCodeSymbol.blank :: leftRev) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem rowBlanks_computes
    (rowCount : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .rowBlanks leftRev
        (List.append
          (List.replicate rowCount MachineCodeSymbol.blank) suffix))
      (config .rowBlanks
        (List.append
          (List.replicate rowCount MachineCodeSymbol.blank).reverse
          leftRev)
        suffix) := by
  induction rowCount generalizing leftRev with
  | zero => exact TuringMachine.Computes.refl _
  | succ rowCount ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (rowBlank_step leftRev
                (List.append
                  (List.replicate rowCount MachineCodeSymbol.blank)
                  suffix)))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
              ih (MachineCodeSymbol.blank :: leftRev))

def optionCursorTape
    (leftCells : List (Option MachineCodeSymbol))
    (rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] => { left := leftCells, head := none, right := [] }
  | current :: remaining =>
      { left := leftCells
        head := some current
        right := remaining.map some }

def optionConfig
    (state : Control)
    (leftCells : List (Option MachineCodeSymbol))
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state, tape := optionCursorTape leftCells rest }

theorem counterSeparator_step
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .rowBlanks leftRev
          (MachineCodeSymbol.done :: rest)) =
      some
        (optionConfig .table (none :: leftRev.map some) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem table_symbol_step
    (leftCells : List (Option MachineCodeSymbol))
    (rest : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (optionConfig .table leftCells (symbol :: rest)) =
      some
        (optionConfig .table (some symbol :: leftCells) rest) := by
  cases symbol <;> cases rest <;>
    simp_all [optionConfig, optionCursorTape, machine,
      transition, TuringMachine.stepConfig, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem table_computes
    (table : Word MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table) :
    TuringMachine.Computes machine
      (optionConfig .table leftCells
        (List.append table
          (MachineCodeSymbol.header :: suffix)))
      (optionConfig .table
        (List.append
          (table.reverse.map (fun symbol => some symbol)) leftCells)
        (MachineCodeSymbol.header :: suffix)) := by
  induction table generalizing leftCells with
  | nil => exact TuringMachine.Computes.refl _
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ MachineCodeSymbol.header :=
        hnoHeader symbol (List.Mem.head rest)
      have hrest : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader rest := by
        intro current hmem
        exact hnoHeader current (List.Mem.tail symbol hmem)
      exact TuringMachine.Computes.step
        (by
          simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
            (table_symbol_step leftCells
              (List.append rest
                (MachineCodeSymbol.header :: suffix))
              symbol hsymbol))
        (by
          simpa [List.reverse_cons, List.map_append,
            List.append_assoc] using
              ih (some symbol :: leftCells) hrest)

theorem insertGap_step
    (leftCells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (optionConfig .table leftCells
          (MachineCodeSymbol.header :: suffix)) =
      some
        (optionConfig (.shift MachineCodeSymbol.header)
          (none :: leftCells) suffix) := by
  cases leftCells <;> cases suffix <;> rfl

def atEndConfig
    (leftCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .atEnd
    tape := { left := leftCells, head := none, right := [] } }

theorem shift_symbol_step
    (carried current : MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol))
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (optionConfig (.shift carried) leftCells (current :: rest)) =
      some
        (optionConfig (.shift current)
          (some carried :: leftCells) rest) := by
  cases carried <;> cases current <;> cases leftCells <;>
    cases rest <;> rfl

theorem shift_none_step
    (carried : MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (optionConfig (.shift carried) leftCells []) =
      some (atEndConfig (some carried :: leftCells)) := by
  cases carried <;> cases leftCells <;> rfl

theorem shift_computes
    (carried : MachineCodeSymbol)
    (remaining : Word MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes machine
      (optionConfig (.shift carried) leftCells remaining)
      (atEndConfig
        (List.append
          ((carried :: remaining).reverse.map
            (fun symbol => some symbol)) leftCells)) := by
  induction remaining generalizing carried leftCells with
  | nil =>
      exact TuringMachine.Computes.step
        (by
          simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
            (shift_none_step carried leftCells))
        (TuringMachine.Computes.refl _)
  | cons current rest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (shift_symbol_step carried current leftCells rest))
        (by
          simpa [List.reverse_cons, List.map_append,
            List.append_assoc] using
              ih current (some carried :: leftCells))

def rewindTape
    (baseLeftCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := baseLeftCells
        head := none
        right := List.append (crossed.map some) [none] }
  | current :: rest =>
      { left := List.append (rest.map some) (none :: baseLeftCells)
        head := some current
        right := List.append (crossed.map some) [none] }

def rewindConfig
    (baseLeftCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rewindSuffix
    tape := rewindTape baseLeftCells remainingRev crossed }

theorem atEnd_step
    (current : MachineCodeSymbol)
    (remainingCells baseLeftCells :
      List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (atEndConfig
          (some current ::
            List.append remainingCells (none :: baseLeftCells))) =
      some
        { state := .rewindSuffix
          tape :=
            { left := List.append remainingCells (none :: baseLeftCells)
              head := some current
              right := [none] } } := by
  cases current <;> cases remainingCells <;> cases baseLeftCells <;> rfl

theorem atEnd_to_rewind_step
    (baseLeftCells : List (Option MachineCodeSymbol))
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (atEndConfig
          (List.append
            ((MachineCodeSymbol.header :: tail).reverse.map
              (fun symbol => some symbol))
            (none :: baseLeftCells))) =
      some
        (rewindConfig baseLeftCells
          (MachineCodeSymbol.header :: tail).reverse []) := by
  cases hrev : (MachineCodeSymbol.header :: tail).reverse with
  | nil => simp at hrev
  | cons current remaining =>
      simpa [rewindConfig, rewindTape, hrev, List.map_append,
        List.append_assoc] using
        atEnd_step current (remaining.map (fun symbol => some symbol))
          baseLeftCells

theorem rewind_symbol_step
    (baseLeftCells : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig baseLeftCells
          (current :: remainingRev) crossed) =
      some
        (rewindConfig baseLeftCells remainingRev
          (current :: crossed)) := by
  cases current <;> cases remainingRev <;> cases crossed <;>
    cases baseLeftCells <;> rfl

theorem rewind_to_gap_computes
    (baseLeftCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (rewindConfig baseLeftCells remainingRev crossed)
      (rewindConfig baseLeftCells []
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil => exact TuringMachine.Computes.refl _
  | cons current remainingRev ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (rewind_symbol_step baseLeftCells current remainingRev crossed))
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (current :: crossed))

def bounceConfig
    (baseLeftCells : List (Option MachineCodeSymbol))
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .bounce
    tape :=
      { left := none :: baseLeftCells
        head := some MachineCodeSymbol.header
        right := List.append (tail.map some) [none] } }

def readyConfig
    (baseLeftCells : List (Option MachineCodeSymbol))
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready
    tape :=
      { left := baseLeftCells
        head := none
        right := List.append
          ((MachineCodeSymbol.header :: tail).map some) [none] } }

theorem rewind_finish_step
    (baseLeftCells : List (Option MachineCodeSymbol))
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig baseLeftCells []
          (MachineCodeSymbol.header :: tail)) =
      some (bounceConfig baseLeftCells tail) := by
  cases baseLeftCells <;> cases tail <;> rfl

theorem bounce_finish_step
    (baseLeftCells : List (Option MachineCodeSymbol))
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig (bounceConfig baseLeftCells tail) =
      some (readyConfig baseLeftCells tail) := by
  cases baseLeftCells <;> cases tail <;> rfl

theorem rewind_suffix_computes
    (baseLeftCells : List (Option MachineCodeSymbol))
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (rewindConfig baseLeftCells
        (MachineCodeSymbol.header :: tail).reverse [])
      (readyConfig baseLeftCells tail) := by
  have hrewind := rewind_to_gap_computes baseLeftCells
    (MachineCodeSymbol.header :: tail).reverse []
  have hfinish := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (rewind_finish_step baseLeftCells tail))
    (TuringMachine.Computes.step
      (TuringMachine.stepConfig_eq_some_iff_step.mp
        (bounce_finish_step baseLeftCells tail))
      (TuringMachine.Computes.refl _))
  exact TuringMachine.computes_trans (by simpa using hrewind) hfinish

theorem sourceConfig_eq_frontConfig
    (fuel stateCount start halt rowCount : Nat)
    (table suffix : Word MachineCodeSymbol) :
    sourceConfig fuel stateCount start halt rowCount table suffix =
      config .fuel []
        (sourceWord fuel stateCount start halt rowCount table suffix) := by
  cases fuel <;> rfl

def masterLeftCells
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append (table.reverse.map some)
    (none ::
      (baseLeftRev fuel stateCount start halt rowCount).map some)

theorem readyConfig_eq_targetConfig
    (fuel stateCount start halt rowCount : Nat)
    (table tail : Word MachineCodeSymbol) :
    readyConfig
        (masterLeftCells fuel stateCount start halt rowCount table) tail =
      targetConfig fuel stateCount start halt rowCount table
        (MachineCodeSymbol.header :: tail) := by
  rfl

theorem canonical_computes
    (fuel stateCount start halt rowCount : Nat)
    (table tail : Word MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table) :
    TuringMachine.Computes machine
      (sourceConfig fuel stateCount start halt rowCount table
        (MachineCodeSymbol.header :: tail))
      (targetConfig fuel stateCount start halt rowCount table
        (MachineCodeSymbol.header :: tail)) := by
  let metadataRev :=
    (metadataWithHalt fuel stateCount start halt).reverse
  let beforeRows := MachineCodeSymbol.blank :: metadataRev
  let base := baseLeftRev fuel stateCount start halt rowCount
  let leftCells := masterLeftCells
    fuel stateCount start halt rowCount table
  have hmetadata := metadata_scan_computes fuel stateCount start halt
    (MachineCodeSymbol.blank ::
      List.append (List.replicate rowCount MachineCodeSymbol.blank)
        (MachineCodeSymbol.done ::
          List.append table (MachineCodeSymbol.header :: tail)))
  have hmetadata' : TuringMachine.Computes machine
      (sourceConfig fuel stateCount start halt rowCount table
        (MachineCodeSymbol.header :: tail))
      (config .oldSeparator metadataRev
        (MachineCodeSymbol.blank ::
          List.append (List.replicate rowCount MachineCodeSymbol.blank)
            (MachineCodeSymbol.done ::
              List.append table
                (MachineCodeSymbol.header :: tail)))) := by
    rw [sourceConfig_eq_frontConfig]
    simpa [sourceWord, metadataRev, List.append_assoc] using hmetadata
  have hold := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (oldSeparator_step metadataRev
        (List.append (List.replicate rowCount MachineCodeSymbol.blank)
          (MachineCodeSymbol.done ::
            List.append table (MachineCodeSymbol.header :: tail)))))
    (TuringMachine.Computes.refl _)
  have hold' : TuringMachine.Computes machine
      (config .oldSeparator metadataRev
        (MachineCodeSymbol.blank ::
          List.append (List.replicate rowCount MachineCodeSymbol.blank)
            (MachineCodeSymbol.done ::
              List.append table
                (MachineCodeSymbol.header :: tail))))
      (config .rowBlanks beforeRows
        (List.append (List.replicate rowCount MachineCodeSymbol.blank)
          (MachineCodeSymbol.done ::
            List.append table (MachineCodeSymbol.header :: tail)))) := by
    simpa [beforeRows] using hold
  have hrows := rowBlanks_computes rowCount beforeRows
    (MachineCodeSymbol.done ::
      List.append table (MachineCodeSymbol.header :: tail))
  have hrows' : TuringMachine.Computes machine
      (config .rowBlanks beforeRows
        (List.append (List.replicate rowCount MachineCodeSymbol.blank)
          (MachineCodeSymbol.done ::
            List.append table (MachineCodeSymbol.header :: tail))))
      (config .rowBlanks base
        (MachineCodeSymbol.done ::
          List.append table (MachineCodeSymbol.header :: tail))) := by
    simpa [base, baseLeftRev, beforeRows, metadataRev,
      List.reverse_replicate] using hrows
  have hcounter := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (counterSeparator_step base
        (List.append table (MachineCodeSymbol.header :: tail))))
    (TuringMachine.Computes.refl _)
  have htable := table_computes table
    (none :: base.map some) tail hnoHeader
  have htable' : TuringMachine.Computes machine
      (optionConfig .table (none :: base.map some)
        (List.append table (MachineCodeSymbol.header :: tail)))
      (optionConfig .table leftCells
        (MachineCodeSymbol.header :: tail)) := by
    simpa [leftCells, masterLeftCells, base] using htable
  have hgap := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (insertGap_step leftCells tail))
    (TuringMachine.Computes.refl _)
  have hshift := shift_computes MachineCodeSymbol.header tail
    (none :: leftCells)
  have hend := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (atEnd_to_rewind_step leftCells tail))
    (TuringMachine.Computes.refl _)
  have hrewind := rewind_suffix_computes leftCells tail
  have hrun := TuringMachine.computes_trans hmetadata' hold'
  have hrun := TuringMachine.computes_trans hrun hrows'
  have hrun := TuringMachine.computes_trans hrun hcounter
  have hrun := TuringMachine.computes_trans hrun htable'
  have hrun := TuringMachine.computes_trans hrun hgap
  have hrun := TuringMachine.computes_trans hrun hshift
  have hrun := TuringMachine.computes_trans hrun hend
  have hrun := TuringMachine.computes_trans hrun hrewind
  change TuringMachine.Computes machine _
    (readyConfig
      (masterLeftCells fuel stateCount start halt rowCount table) tail) at hrun
  rw [readyConfig_eq_targetConfig] at hrun
  exact hrun

theorem computes_of_tape_equiv
    (fuel stateCount start halt rowCount : Nat)
    (table tail : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table)
    (hsource : Tape.Equiv
      (sourceConfig fuel stateCount start halt rowCount table
        (MachineCodeSymbol.header :: tail)).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .fuel, tape := sourceTape }
        { state := .ready, tape := targetTape } ∧
      Tape.Equiv
        (targetConfig fuel stateCount start halt rowCount table
          (MachineCodeSymbol.header :: tail)).tape
        targetTape := by
  have hcanonical := canonical_computes
    fuel stateCount start halt rowCount table tail hnoHeader
  rcases TuringMachine.computes_to_computesIn hcanonical with
    ⟨steps, hcanonicalIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalIn hsource with
    ⟨target, hrun, hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only at hstate
  subst targetState
  refine ⟨targetTape, ?_, htape⟩
  simpa [sourceConfig, targetConfig] using
    TuringMachine.computesIn_to_computes hrun


end Machine

end FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter

end Computability
end FoC

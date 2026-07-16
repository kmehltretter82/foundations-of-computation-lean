import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Materialize

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextLocator

open FiniteRecognizer ExactFuel StrictProbe
open FiniteRecognizer.Interpreter.RuntimeEncodedList

/-!
# Boolean-context locator

Each `Prepend` phase rewinds to the far-left physical blank. This locator walks
the parser word to the right-context count. It crosses the fuel field, header,
state-count/start/halt fields, parser separator, row-count blanks, encoded
counter terminator, raw transition table, context marker, and empty left-list
count. It stops on the right-list count consumed by `Prepend`.
-/

inductive Control where
  | fuel
  | needHeader
  | stateCount
  | startState
  | haltState
  | separator
  | rowBlanks
  | table
  | leftDone
  | ready
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.fuel, .needHeader, .stateCount, .startState, .haltState,
    .separator, .rowBlanks, .table, .leftDone, .ready]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

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
      some (some MachineCodeSymbol.done, Direction.right, .separator)
  | .separator, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .rowBlanks)
  | .rowBlanks, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .rowBlanks)
  | .rowBlanks, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .table)
  | .table, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .leftDone)
  | .table, some symbol =>
      some (some symbol, Direction.right, .table)
  | .leftDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .ready)
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
    (htransition : transition state (some symbol) =
      some (some symbol, Direction.right, next)) :
    TuringMachine.Step machine
      (config state leftRev (symbol :: rest))
      (config next (symbol :: leftRev) rest) := by
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
        (cursor_step state next leftRev suffix MachineCodeSymbol.done hdone)
        (TuringMachine.Computes.refl _)
  | succ count ih =>
      have hstep := cursor_step state state leftRev
        (MachineDescription.encodeNatAppend count suffix)
        MachineCodeSymbol.tick htick
      have hrest := ih (MachineCodeSymbol.tick :: leftRev)
      exact TuringMachine.Computes.step
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using hstep)
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat, List.append_assoc] using hrest)

theorem scanBlanksThenDone_computes
    (count : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .rowBlanks leftRev
        (List.append
          (List.replicate count MachineCodeSymbol.blank)
          (MachineCodeSymbol.done :: suffix)))
      (config .table
        (MachineCodeSymbol.done ::
          List.append
            (List.replicate count MachineCodeSymbol.blank) leftRev)
        suffix) := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (cursor_step .rowBlanks .table leftRev suffix
          MachineCodeSymbol.done rfl)
        (TuringMachine.Computes.refl _)
  | succ count ih =>
      have hstep := cursor_step .rowBlanks .rowBlanks leftRev
        (List.append
          (List.replicate count MachineCodeSymbol.blank)
          (MachineCodeSymbol.done :: suffix))
        MachineCodeSymbol.blank rfl
      have hrest := ih (MachineCodeSymbol.blank :: leftRev)
      have hcommute :=
        list_replicate_append_cons_eq_cons_append
          MachineCodeSymbol.blank count leftRev
      exact TuringMachine.Computes.step
        (by simpa [List.replicate_succ] using hstep)
        (by
          simpa [List.replicate_succ, hcommute,
            List.append_assoc] using hrest)

def noHeader (word : Word MachineCodeSymbol) : Prop :=
  forall (symbol : MachineCodeSymbol),
    List.Mem symbol word -> symbol ≠ MachineCodeSymbol.header

theorem scanTableThenHeader_computes
    (table : Word MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol)
    (hnoHeader : noHeader table) :
    TuringMachine.Computes machine
      (config .table leftRev
        (List.append table (MachineCodeSymbol.header :: suffix)))
      (config .leftDone
        (MachineCodeSymbol.header ::
          List.append table.reverse leftRev)
        suffix) := by
  induction table generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.step
        (cursor_step .table .leftDone leftRev suffix
          MachineCodeSymbol.header rfl)
        (TuringMachine.Computes.refl _)
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ MachineCodeSymbol.header :=
        hnoHeader symbol (List.Mem.head rest)
      have hrest : noHeader rest := by
        intro current hmem
        exact hnoHeader current (List.Mem.tail symbol hmem)
      have htransition :
          transition .table (some symbol) =
            some (some symbol, Direction.right, .table) := by
        cases symbol <;> simp_all [transition]
      have hstep := cursor_step .table .table leftRev
        (List.append rest (MachineCodeSymbol.header :: suffix))
        symbol htransition
      have hrun := ih (symbol :: leftRev) hrest
      exact TuringMachine.Computes.step
        (by simpa using hstep)
        (by
          simpa [List.reverse_cons, List.append_assoc] using hrun)

def parserTailBeforeRightCount
    (rowCount : Nat)
    (table : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.blank ::
    List.append
      (List.replicate rowCount MachineCodeSymbol.blank)
      (MachineCodeSymbol.done ::
        List.append table
          [MachineCodeSymbol.header, MachineCodeSymbol.done])

def parsedMetadataAppend
    (fuel stateCount start halt : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend fuel
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend stateCount
        (MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt suffix)))

def rightCountPrefix
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  parsedMetadataAppend fuel stateCount start halt
    (parserTailBeforeRightCount rowCount table)

def locatorWord
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (rightCountPrefix fuel stateCount start halt rowCount table)
    (MachineDescription.encodeNatAppend rightCount suffix)

def rightCountBaseLeftRev
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  (rightCountPrefix fuel stateCount start halt rowCount table).reverse

def sourceConfig
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .fuel []
    (locatorWord fuel stateCount start halt rowCount table rightCount
      suffix)

def targetConfig
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .ready
    (rightCountBaseLeftRev fuel stateCount start halt rowCount table)
    (MachineDescription.encodeNatAppend rightCount suffix)

theorem target_tape_eq_prepend_source
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    (targetConfig fuel stateCount start halt rowCount table rightCount
      suffix).tape =
      (Prepend.sourceConfig
        (rightCountBaseLeftRev fuel stateCount start halt rowCount table)
        rightCount suffix).tape := by
  rfl

theorem computes_to_right_count
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (rightCount : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnoHeader : noHeader table) :
    TuringMachine.Computes machine
      (sourceConfig fuel stateCount start halt rowCount table rightCount
        suffix)
      (targetConfig fuel stateCount start halt rowCount table rightCount
        suffix) := by
  let afterFuel : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat fuel).reverse []
  let afterHeader : Word MachineCodeSymbol :=
    MachineCodeSymbol.header :: afterFuel
  let afterStateCount : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat stateCount).reverse afterHeader
  let afterStart : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat start).reverse afterStateCount
  let afterHalt : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat halt).reverse afterStart
  let afterSeparator : Word MachineCodeSymbol :=
    MachineCodeSymbol.blank :: afterHalt
  let afterRows : Word MachineCodeSymbol :=
    MachineCodeSymbol.done ::
      List.append
        (List.replicate rowCount MachineCodeSymbol.blank) afterSeparator
  let afterTable : Word MachineCodeSymbol :=
    MachineCodeSymbol.header :: List.append table.reverse afterRows
  have hfuel := scanUnary_computes .fuel .needHeader rfl rfl fuel []
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend stateCount
        (MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt
            (MachineCodeSymbol.blank ::
              List.append
                (List.replicate rowCount MachineCodeSymbol.blank)
                (MachineCodeSymbol.done ::
                  List.append table
                    (MachineCodeSymbol.header ::
                      MachineCodeSymbol.done ::
                      MachineDescription.encodeNatAppend rightCount
                        suffix))))))
  have hheader : TuringMachine.Computes machine
      (config .needHeader afterFuel
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineCodeSymbol.blank ::
                  List.append
                    (List.replicate rowCount MachineCodeSymbol.blank)
                    (MachineCodeSymbol.done ::
                      List.append table
                        (MachineCodeSymbol.header ::
                          MachineCodeSymbol.done ::
                          MachineDescription.encodeNatAppend rightCount
                            suffix)))))))
      (config .stateCount afterHeader
        (MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt
              (MachineCodeSymbol.blank ::
                List.append
                  (List.replicate rowCount MachineCodeSymbol.blank)
                  (MachineCodeSymbol.done ::
                    List.append table
                      (MachineCodeSymbol.header ::
                        MachineCodeSymbol.done ::
                        MachineDescription.encodeNatAppend rightCount
                          suffix))))))) := by
    exact TuringMachine.Computes.step
      (cursor_step .needHeader .stateCount afterFuel _
        MachineCodeSymbol.header rfl)
      (TuringMachine.Computes.refl _)
  have hstateCount := scanUnary_computes .stateCount .startState rfl rfl
    stateCount afterHeader
    (MachineDescription.encodeNatAppend start
      (MachineDescription.encodeNatAppend halt
        (MachineCodeSymbol.blank ::
          List.append
            (List.replicate rowCount MachineCodeSymbol.blank)
            (MachineCodeSymbol.done ::
              List.append table
                (MachineCodeSymbol.header :: MachineCodeSymbol.done ::
                  MachineDescription.encodeNatAppend rightCount suffix)))))
  have hstart := scanUnary_computes .startState .haltState rfl rfl
    start afterStateCount
    (MachineDescription.encodeNatAppend halt
      (MachineCodeSymbol.blank ::
        List.append
          (List.replicate rowCount MachineCodeSymbol.blank)
          (MachineCodeSymbol.done ::
            List.append table
              (MachineCodeSymbol.header :: MachineCodeSymbol.done ::
                MachineDescription.encodeNatAppend rightCount suffix))))
  have hhalt := scanUnary_computes .haltState .separator rfl rfl
    halt afterStart
    (MachineCodeSymbol.blank ::
      List.append
        (List.replicate rowCount MachineCodeSymbol.blank)
        (MachineCodeSymbol.done ::
          List.append table
            (MachineCodeSymbol.header :: MachineCodeSymbol.done ::
              MachineDescription.encodeNatAppend rightCount suffix)))
  have hseparator : TuringMachine.Computes machine
      (config .separator afterHalt
        (MachineCodeSymbol.blank ::
          List.append
            (List.replicate rowCount MachineCodeSymbol.blank)
            (MachineCodeSymbol.done ::
              List.append table
                (MachineCodeSymbol.header :: MachineCodeSymbol.done ::
                  MachineDescription.encodeNatAppend rightCount suffix))))
      (config .rowBlanks afterSeparator
        (List.append
          (List.replicate rowCount MachineCodeSymbol.blank)
          (MachineCodeSymbol.done ::
            List.append table
              (MachineCodeSymbol.header :: MachineCodeSymbol.done ::
                MachineDescription.encodeNatAppend rightCount suffix)))) := by
    exact TuringMachine.Computes.step
      (cursor_step .separator .rowBlanks afterHalt _
        MachineCodeSymbol.blank rfl)
      (TuringMachine.Computes.refl _)
  have hrows := scanBlanksThenDone_computes rowCount afterSeparator
    (List.append table
      (MachineCodeSymbol.header :: MachineCodeSymbol.done ::
        MachineDescription.encodeNatAppend rightCount suffix))
  have htable := scanTableThenHeader_computes table afterRows
    (MachineCodeSymbol.done ::
      MachineDescription.encodeNatAppend rightCount suffix) hnoHeader
  have hleftDone : TuringMachine.Computes machine
      (config .leftDone afterTable
        (MachineCodeSymbol.done ::
          MachineDescription.encodeNatAppend rightCount suffix))
      (config .ready (MachineCodeSymbol.done :: afterTable)
        (MachineDescription.encodeNatAppend rightCount suffix)) := by
    exact TuringMachine.Computes.step
      (cursor_step .leftDone .ready afterTable _
        MachineCodeSymbol.done rfl)
      (TuringMachine.Computes.refl _)
  have hrun := TuringMachine.computes_trans hfuel hheader
  have hrun := TuringMachine.computes_trans hrun hstateCount
  have hrun := TuringMachine.computes_trans hrun hstart
  have hrun := TuringMachine.computes_trans hrun hhalt
  have hrun := TuringMachine.computes_trans hrun hseparator
  have hrun := TuringMachine.computes_trans hrun hrows
  have hrun := TuringMachine.computes_trans hrun htable
  have hrun := TuringMachine.computes_trans hrun hleftDone
  simpa [sourceConfig, targetConfig, locatorWord,
    rightCountBaseLeftRev, rightCountPrefix, parsedMetadataAppend,
    parserTailBeforeRightCount, MachineDescription.encodeNatAppend,
    List.reverse_append, afterFuel, afterHeader, afterStateCount,
    afterStart, afterHalt, afterSeparator, afterRows, afterTable,
    List.append_assoc] using hrun


end FiniteRecognizer.Interpreter.BooleanContextLocator

end Computability
end FoC

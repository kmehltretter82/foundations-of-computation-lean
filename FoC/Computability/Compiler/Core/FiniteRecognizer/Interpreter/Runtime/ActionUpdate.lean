import FoC.Computability.MachineBuilder.Encoding

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimeActionPrefix

/-!
**Selected-row action handoff.** This finite prefix consumes a canonical
selected transition through its dynamically encoded source, read, write, and
direction fields. Its endpoint stores the finite write/move action in control
and positions the head at the first token of the dynamic target-state field.
The target unary field stays on tape for the runtime configuration materializer,
so no unbounded state is placed in finite control.
-/

inductive Control where
  | needTransition
  | scanSource
  | needRead
  | needWrite
  | needDirection (write : Option Bool)
  | ready (write : Option Bool) (move : Direction)
  | halt
deriving DecidableEq

namespace Control

def optionBools : List (Option Bool) :=
  [none, some false, some true]

def directions : List Direction :=
  [Direction.left, Direction.right]

theorem optionBools_complete (cell : Option Bool) :
    cell ∈ optionBools := by
  cases cell with
  | none => simp [optionBools]
  | some bit =>
      cases bit <;> simp [optionBools]

theorem directions_complete (move : Direction) :
    move ∈ directions := by
  cases move <;> simp [directions]

def readyControls : List Control :=
  optionBools.flatMap
    (fun write => directions.map (Control.ready write))

def elems : List Control :=
  [needTransition, scanSource, needRead, needWrite, halt] ++
    optionBools.map needDirection ++ readyControls

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro state
    cases state with
    | needTransition => simp [elems]
    | scanSource => simp [elems]
    | needRead => simp [elems]
    | needWrite => simp [elems]
    | needDirection write =>
        simp [elems, optionBools_complete write]
    | ready write move =>
        simp [elems, readyControls, optionBools_complete write,
          directions_complete move]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .needTransition, some MachineCodeSymbol.transition =>
      some
        (some MachineCodeSymbol.transition, Direction.right,
          .scanSource)
  | .scanSource, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .scanSource)
  | .scanSource, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .needRead)
  | .needRead, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .needWrite)
  | .needRead, some MachineCodeSymbol.zero =>
      some (some MachineCodeSymbol.zero, Direction.right, .needWrite)
  | .needRead, some MachineCodeSymbol.one =>
      some (some MachineCodeSymbol.one, Direction.right, .needWrite)
  | .needWrite, some MachineCodeSymbol.blank =>
      some
        (some MachineCodeSymbol.blank, Direction.right,
          .needDirection none)
  | .needWrite, some MachineCodeSymbol.zero =>
      some
        (some MachineCodeSymbol.zero, Direction.right,
          .needDirection (some false))
  | .needWrite, some MachineCodeSymbol.one =>
      some
        (some MachineCodeSymbol.one, Direction.right,
          .needDirection (some true))
  | .needDirection write, some MachineCodeSymbol.moveLeft =>
      some
        (some MachineCodeSymbol.moveLeft, Direction.right,
          .ready write Direction.left)
  | .needDirection write, some MachineCodeSymbol.moveRight =>
      some
        (some MachineCodeSymbol.moveRight, Direction.right,
          .ready write Direction.right)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .needTransition
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def tapeAtWords
    (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftRev.map some
        head := none
        right := [] }
  | first :: tail =>
      { left := leftRev.map some
        head := some first
        right := tail.map some }

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .needTransition
  tape := tapeAtWords baseLeftRev
    (MachineDescription.encodeTransitionAppend selected suffix)

def consumedPrefix
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  MachineCodeSymbol.transition ::
    MachineDescription.encodeNatAppend selected.source
      (MachineDescription.encodeCellAppend selected.read
        (MachineDescription.encodeCellAppend selected.write
          (MachineDescription.encodeDirection selected.move)))

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready selected.write selected.move
  tape := tapeAtWords
    (List.append (consumedPrefix selected).reverse baseLeftRev)
    (MachineDescription.encodeNatAppend selected.target suffix)

def runSteps (selected : TransitionDescription) : Nat :=
  (1 + (selected.source + 1)) + 3

theorem tapeAtWords_write_move_right
    (leftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write (some first)
          (tapeAtWords leftRev (first :: rest))) =
      tapeAtWords (first :: leftRev) rest := by
  cases rest
  all_goals rfl
  done

theorem step_needTransition
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig (sourceConfig baseLeftRev selected suffix) =
      some
        { state := .scanSource
          tape := tapeAtWords
            (MachineCodeSymbol.transition :: baseLeftRev)
            (MachineDescription.encodeNatAppend selected.source
              (MachineDescription.encodeCellAppend selected.read
                (MachineDescription.encodeCellAppend selected.write
                  (MachineDescription.encodeDirectionAppend selected.move
                    (MachineDescription.encodeNatAppend selected.target
                      suffix))))) } := by
  cases selected with
  | mk source read write move target =>
      cases source
      all_goals rfl
  done

def scanSourceConfig
    (leftRev : Word MachineCodeSymbol)
    (source : Nat)
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scanSource
  tape := tapeAtWords leftRev
    (MachineDescription.encodeNatAppend source tail)

def afterSourceConfig
    (leftRev : Word MachineCodeSymbol)
    (source : Nat)
    (tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .needRead
  tape := tapeAtWords
    (List.append (MachineDescription.encodeNat source).reverse leftRev)
    tail

theorem step_scanSource_succ
    (leftRev : Word MachineCodeSymbol)
    (source : Nat)
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanSourceConfig leftRev (source + 1) tail) =
      some
        (scanSourceConfig
          (MachineCodeSymbol.tick :: leftRev) source tail) := by
  cases source
  all_goals rfl
  done

theorem scanSource_run_exact
    (leftRev : Word MachineCodeSymbol)
    (source : Nat)
    (tail : Word MachineCodeSymbol) :
    machine.runConfigExact? (source + 1)
        (scanSourceConfig leftRev source tail) =
      some (afterSourceConfig leftRev source tail) := by
  induction source generalizing leftRev
  case zero =>
    cases tail <;> rfl
  case succ source ih =>
    rw [TuringMachine.runConfigExact?]
    rw [step_scanSource_succ]
    simp only
    rw [ih]
    simp [afterSourceConfig, MachineDescription.encodeNat,
      List.reverse_cons, List.append_assoc]
  done

def actionFieldsSourceConfig
    (leftRev : Word MachineCodeSymbol)
    (read write : Option Bool)
    (move : Direction)
    (target : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .needRead
  tape := tapeAtWords leftRev
    (MachineDescription.encodeCellAppend read
      (MachineDescription.encodeCellAppend write
        (MachineDescription.encodeDirectionAppend move
          (MachineDescription.encodeNatAppend target suffix))))

def actionFieldsTargetConfig
    (leftRev : Word MachineCodeSymbol)
    (write : Option Bool)
    (move : Direction)
    (target : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready write move
  tape := tapeAtWords
    (MachineDescription.encodeDirectionAppend move
      (MachineDescription.encodeCellAppend write leftRev))
    (MachineDescription.encodeNatAppend target suffix)

def configAt
    (state : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := state
  tape := tapeAtWords leftRev rest

theorem step_needRead_field
    (leftRev : Word MachineCodeSymbol)
    (read : Option Bool)
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (configAt .needRead leftRev
          (MachineDescription.encodeCellAppend read tail)) =
      some
        (configAt .needWrite
          (MachineDescription.encodeCellAppend read leftRev) tail) := by
  cases read with
  | none => cases tail <;> rfl
  | some read =>
      cases read <;> cases tail <;> rfl
  done

theorem step_needWrite_field
    (leftRev : Word MachineCodeSymbol)
    (write : Option Bool)
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (configAt .needWrite leftRev
          (MachineDescription.encodeCellAppend write tail)) =
      some
        (configAt (.needDirection write)
          (MachineDescription.encodeCellAppend write leftRev) tail) := by
  cases write with
  | none => cases tail <;> rfl
  | some write =>
      cases write <;> cases tail <;> rfl
  done

theorem step_needDirection_field
    (leftRev : Word MachineCodeSymbol)
    (write : Option Bool)
    (move : Direction)
    (tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (configAt (.needDirection write) leftRev
          (MachineDescription.encodeDirectionAppend move tail)) =
      some
        (configAt (.ready write move)
          (MachineDescription.encodeDirectionAppend move leftRev)
          tail) := by
  cases move <;> cases tail <;> rfl
  done

theorem actionFields_run_exact
    (leftRev : Word MachineCodeSymbol)
    (read write : Option Bool)
    (move : Direction)
    (target : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 3
        (actionFieldsSourceConfig leftRev read write move target suffix) =
      some
        (actionFieldsTargetConfig
          (MachineDescription.encodeCellAppend read leftRev)
          write move target suffix) := by
  change
    machine.runConfigExact? 3
        (configAt .needRead leftRev
          (MachineDescription.encodeCellAppend read
            (MachineDescription.encodeCellAppend write
              (MachineDescription.encodeDirectionAppend move
                (MachineDescription.encodeNatAppend target suffix))))) =
      some
        (configAt (.ready write move)
          (MachineDescription.encodeDirectionAppend move
          (MachineDescription.encodeCellAppend write
              (MachineDescription.encodeCellAppend read leftRev)))
          (MachineDescription.encodeNatAppend target suffix))
  rw [TuringMachine.runConfigExact?]
  rw [step_needRead_field]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [step_needWrite_field]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [step_needDirection_field]
  rfl
  done

theorem runConfigExact_trans
    {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol Control}
    (hab : machine.runConfigExact? first a = some b)
    (hbc : machine.runConfigExact? second b = some c) :
    machine.runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)
  done

def actionTail
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellAppend selected.read
    (MachineDescription.encodeCellAppend selected.write
      (MachineDescription.encodeDirectionAppend selected.move
        (MachineDescription.encodeNatAppend selected.target suffix)))

theorem transition_entry_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 1
        (sourceConfig baseLeftRev selected suffix) =
      some
        (scanSourceConfig
          (MachineCodeSymbol.transition :: baseLeftRev)
          selected.source (actionTail selected suffix)) := by
  rw [TuringMachine.runConfigExact?]
  rw [step_needTransition]
  rfl
  done

theorem afterSource_eq_actionFieldsSource
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    afterSourceConfig
        (MachineCodeSymbol.transition :: baseLeftRev)
        selected.source (actionTail selected suffix) =
      actionFieldsSourceConfig
        (List.append
          (MachineDescription.encodeNat selected.source).reverse
          (MachineCodeSymbol.transition :: baseLeftRev))
        selected.read selected.write selected.move selected.target suffix := by
  rfl
  done

theorem encodeCell_reverse (cell : Option Bool) :
    (MachineDescription.encodeCell cell).reverse =
      MachineDescription.encodeCell cell := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl
  done

theorem encodeDirection_reverse (move : Direction) :
    (MachineDescription.encodeDirection move).reverse =
      MachineDescription.encodeDirection move := by
  cases move <;> rfl
  done

theorem actionFieldsTarget_eq_target
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    actionFieldsTargetConfig
        (MachineDescription.encodeCellAppend selected.read
          (List.append
            (MachineDescription.encodeNat selected.source).reverse
            (MachineCodeSymbol.transition :: baseLeftRev)))
        selected.write selected.move selected.target suffix =
      targetConfig baseLeftRev selected suffix := by
  cases selected
  simp [actionFieldsTargetConfig, targetConfig, consumedPrefix,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeDirectionAppend,
    MachineDescription.encodeNatAppend,
    List.reverse_append, encodeCell_reverse, encodeDirection_reverse,
    List.append_assoc]
  done

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (selected : TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps selected)
        (sourceConfig baseLeftRev selected suffix) =
      some (targetConfig baseLeftRev selected suffix) := by
  have hentry :=
    transition_entry_run_exact baseLeftRev selected suffix
  have hsource :=
    scanSource_run_exact
      (MachineCodeSymbol.transition :: baseLeftRev)
      selected.source (actionTail selected suffix)
  rw [afterSource_eq_actionFieldsSource] at hsource
  have hfields :=
    actionFields_run_exact
      (List.append
        (MachineDescription.encodeNat selected.source).reverse
        (MachineCodeSymbol.transition :: baseLeftRev))
      selected.read selected.write selected.move selected.target suffix
  rw [actionFieldsTarget_eq_target] at hfields
  exact runConfigExact_trans (runConfigExact_trans hentry hsource) hfields
  done

end FiniteRecognizer.Interpreter.RuntimeActionPrefix

end Computability
end FoC

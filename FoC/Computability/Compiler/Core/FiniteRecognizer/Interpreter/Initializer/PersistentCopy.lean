import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Basic
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser.Basic

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.InitializerPersistentCopy

open FiniteRecognizer ExactFuel StrictProbe

/-!
# Persistent-master table copier

The source table lies between two physical blank boundaries. The machine
visits its symbols from right to left. For each symbol it uses `header` as a
temporary marker, shifts the protected suffix one cell right, inserts the
copied symbol at the front of that suffix, restores the source symbol, and
advances left. The protected suffix is opaque to the copier, and the
construction uses one permanent separator plus the represented word's
terminal blank.
-/

namespace PersistentMasterCopier

inductive Control where
  | enter
  | seedShift (carried : MachineCodeSymbol)
  | seedAtEnd
  | seedRewind
  | select
  | seekGap (original : MachineCodeSymbol)
  | shift (original carried : MachineCodeSymbol)
  | atEnd (original : MachineCodeSymbol)
  | rewind (original : MachineCodeSymbol)
  | locateSource (original : MachineCodeSymbol)
  | seekMasterEnd
  | ready
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.enter, .seedAtEnd, .seedRewind, .select, .seekMasterEnd, .ready] ++
    MachineCodeSymbol.finite.elems.map seedShift ++
    MachineCodeSymbol.finite.elems.map seekGap ++
    MachineCodeSymbol.finite.elems.flatMap (fun original =>
      MachineCodeSymbol.finite.elems.map (shift original)) ++
    MachineCodeSymbol.finite.elems.map atEnd ++
    MachineCodeSymbol.finite.elems.map rewind ++
    MachineCodeSymbol.finite.elems.map locateSource

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | enter => simp [elems]
    | seedShift carried =>
        simp [elems, MachineCodeSymbol.finite.complete carried]
    | seedAtEnd => simp [elems]
    | seedRewind => simp [elems]
    | select => simp [elems]
    | seekGap original =>
        simp [elems, MachineCodeSymbol.finite.complete original]
    | shift original carried =>
        simp [elems, MachineCodeSymbol.finite.complete original,
          MachineCodeSymbol.finite.complete carried]
    | atEnd original =>
        simp [elems, MachineCodeSymbol.finite.complete original]
    | rewind original =>
        simp [elems, MachineCodeSymbol.finite.complete original]
    | locateSource original =>
        simp [elems, MachineCodeSymbol.finite.complete original]
    | seekMasterEnd => simp [elems]
    | ready => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter, none =>
      some (none, Direction.right, .seedShift MachineCodeSymbol.header)
  | .seedShift carried, some current =>
      some (some carried, Direction.right, .seedShift current)
  | .seedShift carried, none =>
      some (some carried, Direction.right, .seedAtEnd)
  | .seedAtEnd, none => some (none, Direction.left, .seedRewind)
  | .seedRewind, some current =>
      some (some current, Direction.left, .seedRewind)
  | .seedRewind, none => some (none, Direction.left, .select)
  | .select, some current =>
      some (some MachineCodeSymbol.header, Direction.right,
        .seekGap current)
  | .select, none => some (none, Direction.right, .seekMasterEnd)
  | .seekGap original, some current =>
      some (some current, Direction.right, .seekGap original)
  | .seekGap original, none =>
      some (none, Direction.right, .shift original original)
  | .shift original carried, some current =>
      some (some carried, Direction.right, .shift original current)
  | .shift original carried, none =>
      some (some carried, Direction.right, .atEnd original)
  | .atEnd original, none =>
      some (none, Direction.left, .rewind original)
  | .rewind original, some current =>
      some (some current, Direction.left, .rewind original)
  | .rewind original, none =>
      some (none, Direction.left, .locateSource original)
  | .locateSource original, some MachineCodeSymbol.header =>
      some (some original, Direction.left, .select)
  | .locateSource original, some current =>
      some (some current, Direction.left, .locateSource original)
  | .seekMasterEnd, some current =>
      some (some current, Direction.right, .seekMasterEnd)
  | .seekMasterEnd, none =>
      some (none, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .enter
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def tapeAtCells
    (leftRev cells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match cells with
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

def representedCells (word : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  word.map some ++ [none]

def sourceTape
    (baseLeftRev master suffix : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  { left := master.reverse.map some ++ none :: baseLeftRev.map some
    head := none
    right := representedCells suffix }

def sourceConfig
    (baseLeftRev master suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .enter, tape := sourceTape baseLeftRev master suffix }

def selectTape
    (baseLeftRev remainingRev processed suffix : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := baseLeftRev.map some
        head := none
        right := processed.map some ++
          none :: representedCells (List.append processed suffix) }
  | current :: more =>
      { left := more.map some ++ none :: baseLeftRev.map some
        head := some current
        right := processed.map some ++
          none :: representedCells (List.append processed suffix) }

def selectConfig
    (baseLeftRev remainingRev processed suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .select
    tape := selectTape baseLeftRev remainingRev processed suffix }

def seekGapTape
    (baseLeftRev moreRev crossedRev remaining active :
      Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  tapeAtCells
    (crossedRev.map some ++
      some MachineCodeSymbol.header ::
        moreRev.map some ++ none :: baseLeftRev.map some)
    (remaining.map some ++ none :: representedCells active)

def seekGapConfig
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev crossedRev remaining active :
      Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seekGap original
    tape := seekGapTape baseLeftRev moreRev crossedRev remaining active }

def shiftTape
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  tapeAtCells (writtenRev.map some ++ baseCells)
    (representedCells remaining)

def shiftConfig
    (original carried : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .shift original carried
    tape := shiftTape baseCells writtenRev remaining }

def atEndConfig
    (original : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (output : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .atEnd original
    tape :=
      { left := output.reverse.map some ++ baseCells
        head := none
        right := [] } }

def rewindTape
    (baseCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      match baseCells with
      | [] =>
          { left := []
            head := none
            right := crossed.map some ++ [none] }
      | cell :: rest =>
          { left := rest
            head := cell
            right := crossed.map some ++ [none] }
  | current :: more =>
      { left := more.map some ++ baseCells
        head := some current
        right := crossed.map some ++ [none] }

def rewindConfig
    (original : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rewind original
    tape := rewindTape baseCells remainingRev crossed }

def seedShiftConfig
    (carried : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seedShift carried
    tape := shiftTape baseCells writtenRev remaining }

def seedAtEndConfig
    (baseCells : List (Option MachineCodeSymbol))
    (output : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seedAtEnd
    tape :=
      { left := output.reverse.map some ++ baseCells
        head := none
        right := [] } }

def seedRewindConfig
    (baseCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seedRewind
    tape := rewindTape baseCells remainingRev crossed }

def locateSourceTape
    (baseLeftRev moreRev remainingRev crossed output :
      Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := moreRev.map some ++ none :: baseLeftRev.map some
        head := some MachineCodeSymbol.header
        right := crossed.map some ++ none :: representedCells output }
  | current :: more =>
      { left := more.map some ++
          some MachineCodeSymbol.header ::
            moreRev.map some ++ none :: baseLeftRev.map some
        head := some current
        right := crossed.map some ++ none :: representedCells output }

def locateSourceConfig
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev remainingRev crossed output :
      Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .locateSource original
    tape := locateSourceTape baseLeftRev moreRev remainingRev crossed output }

def seekMasterEndTape
    (baseLeftRev crossedRev remaining active : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  tapeAtCells
    (crossedRev.map some ++ none :: baseLeftRev.map some)
    (remaining.map some ++ none :: representedCells active)

def seekMasterEndConfig
    (baseLeftRev crossedRev remaining active : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .seekMasterEnd
    tape := seekMasterEndTape baseLeftRev crossedRev remaining active }

def readyTape
    (baseLeftRev master suffix : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  tapeAtCells
    (none :: master.reverse.map some ++ none :: baseLeftRev.map some)
    (representedCells (List.append master suffix))

def readyConfig
    (baseLeftRev master suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready, tape := readyTape baseLeftRev master suffix }

theorem enter_step
    (baseLeftRev master suffix : Word MachineCodeSymbol) :
    machine.stepConfig (sourceConfig baseLeftRev master suffix) =
      some
        (seedShiftConfig MachineCodeSymbol.header
          (none :: master.reverse.map some ++
            none :: baseLeftRev.map some)
          [] suffix) := by
  cases suffix <;> cases master <;> cases baseLeftRev <;> rfl

theorem seedShift_symbol_step
    (carried current : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    machine.stepConfig
        (seedShiftConfig carried baseCells writtenRev
          (current :: remaining)) =
      some
        (seedShiftConfig current baseCells
          (carried :: writtenRev) remaining) := by
  cases remaining <;> cases writtenRev <;> cases baseCells <;> rfl

theorem seedShift_blank_step
    (carried : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (seedShiftConfig carried baseCells writtenRev []) =
      some
        (seedAtEndConfig baseCells
          (List.append writtenRev.reverse [carried])) := by
  cases writtenRev <;> cases baseCells <;>
    simp [machine, transition, seedShiftConfig, shiftTape,
      seedAtEndConfig, tapeAtCells, representedCells,
      TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
      Tape.moveRight, List.map_append, List.append_assoc]

theorem seedAtEnd_step
    (baseCells : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (seedAtEndConfig baseCells (first :: rest)) =
      some
        (seedRewindConfig baseCells (first :: rest).reverse []) := by
  have hne : (first :: rest).reverse ≠ [] := by simp
  cases hrev : (first :: rest).reverse with
  | nil => contradiction
  | cons current more =>
      simp [machine, transition, seedAtEndConfig, seedRewindConfig,
        rewindTape, TuringMachine.stepConfig, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, hrev]

theorem seedRewind_symbol_step
    (current : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (more crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (seedRewindConfig baseCells (current :: more) crossed) =
      some
        (seedRewindConfig baseCells more (current :: crossed)) := by
  cases more <;> cases crossed <;> cases baseCells <;> rfl

theorem seedRewind_blank_step
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest seededSuffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (seedRewindConfig
          (none :: (first :: rest).reverse.map some ++
            none :: baseLeftRev.map some)
          [] seededSuffix) =
      some
        (selectConfig baseLeftRev (first :: rest).reverse []
          seededSuffix) := by
  have hnonempty : (first :: rest).reverse ≠ [] := by simp
  cases hrev : (first :: rest).reverse with
  | nil => contradiction
  | cons current more =>
      simp [machine, transition, seedRewindConfig, rewindTape,
        selectConfig, selectTape, representedCells,
        TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, hrev, List.map_reverse,
        List.map_append, List.append_assoc]

theorem select_symbol_step
    (baseLeftRev moreRev processed suffix : Word MachineCodeSymbol)
    (current : MachineCodeSymbol) :
    machine.stepConfig
        (selectConfig baseLeftRev (current :: moreRev) processed suffix) =
      some
        (seekGapConfig current baseLeftRev moreRev [] processed
          (List.append processed suffix)) := by
  cases processed <;> cases suffix <;> cases moreRev <;>
    cases baseLeftRev <;> rfl

theorem seekGap_symbol_step
    (original current : MachineCodeSymbol)
    (baseLeftRev moreRev crossedRev remaining active :
      Word MachineCodeSymbol) :
    machine.stepConfig
        (seekGapConfig original baseLeftRev moreRev crossedRev
          (current :: remaining) active) =
      some
        (seekGapConfig original baseLeftRev moreRev
          (current :: crossedRev) remaining active) := by
  cases remaining <;> cases crossedRev <;> cases active <;>
    cases moreRev <;> cases baseLeftRev <;> rfl

theorem seekGap_blank_step
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev sourceRev active : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekGapConfig original baseLeftRev moreRev sourceRev [] active) =
      some
        (shiftConfig original original
          (none :: sourceRev.map some ++
            some MachineCodeSymbol.header ::
              moreRev.map some ++ none :: baseLeftRev.map some)
          [] active) := by
  cases active <;> cases sourceRev <;> cases moreRev <;>
    cases baseLeftRev <;> rfl

theorem shift_symbol_step
    (original carried current : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    machine.stepConfig
        (shiftConfig original carried baseCells writtenRev
          (current :: remaining)) =
      some
        (shiftConfig original current baseCells
          (carried :: writtenRev) remaining) := by
  cases remaining <;> cases writtenRev <;> cases baseCells <;> rfl

theorem shift_blank_step
    (original carried : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (shiftConfig original carried baseCells writtenRev []) =
      some
        (atEndConfig original baseCells
          (List.append writtenRev.reverse [carried])) := by
  cases writtenRev <;> cases baseCells <;>
    simp [machine, transition, shiftConfig, shiftTape, atEndConfig,
      tapeAtCells, representedCells, TuringMachine.stepConfig,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.map_append, List.append_assoc]

theorem atEnd_step
    (original : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (atEndConfig original baseCells (first :: rest)) =
      some
        (rewindConfig original baseCells
          (first :: rest).reverse []) := by
  have hne : (first :: rest).reverse ≠ [] := by simp
  cases hrev : (first :: rest).reverse with
  | nil => contradiction
  | cons current more =>
      simp [machine, transition, atEndConfig, rewindConfig, rewindTape,
        TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, hrev]

theorem rewind_symbol_step
    (original current : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (more crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig original baseCells (current :: more) crossed) =
      some
        (rewindConfig original baseCells more (current :: crossed)) := by
  cases more <;> cases crossed <;> cases baseCells <;> rfl

theorem rewind_blank_step
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev processed output : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig original
          (none :: processed.reverse.map some ++
            some MachineCodeSymbol.header ::
              moreRev.map some ++ none :: baseLeftRev.map some)
          [] output) =
      some
        (locateSourceConfig original baseLeftRev moreRev
          processed.reverse [] output) := by
  cases hrev : processed.reverse with
  | nil =>
      simp [machine, transition, rewindConfig, rewindTape,
        locateSourceConfig, locateSourceTape, representedCells,
        TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, hrev, List.map_append, List.append_assoc]
  | cons current remaining =>
      simp [machine, transition, rewindConfig, rewindTape,
        locateSourceConfig, locateSourceTape, representedCells,
        TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, hrev, List.map_append, List.append_assoc]

theorem locateSource_symbol_step
    (original current : MachineCodeSymbol)
    (baseLeftRev moreRev remainingRev crossed output :
      Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (locateSourceConfig original baseLeftRev moreRev
          (current :: remainingRev) crossed output) =
      some
        (locateSourceConfig original baseLeftRev moreRev
          remainingRev (current :: crossed) output) := by
  cases current <;> simp_all [machine, transition,
    locateSourceConfig, locateSourceTape, representedCells,
    TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft, List.map_append, List.append_assoc] <;>
    cases remainingRev <;> cases crossed <;> cases output <;>
      cases moreRev <;> cases baseLeftRev <;> rfl

theorem locateSource_marker_step
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev processed suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (locateSourceConfig original baseLeftRev moreRev [] processed
          (original :: List.append processed suffix)) =
      some
        (selectConfig baseLeftRev moreRev (original :: processed) suffix) := by
  cases moreRev <;> cases processed <;> cases suffix <;>
    cases baseLeftRev <;>
    simp [machine, transition, locateSourceConfig, locateSourceTape,
      selectConfig, selectTape, representedCells,
      TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.map_append, List.append_assoc]

theorem select_blank_step
    (baseLeftRev processed suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (selectConfig baseLeftRev [] processed suffix) =
      some
        (seekMasterEndConfig baseLeftRev [] processed
          (List.append processed suffix)) := by
  cases processed <;> cases suffix <;> cases baseLeftRev <;> rfl

theorem seekMasterEnd_symbol_step
    (current : MachineCodeSymbol)
    (baseLeftRev crossedRev remaining active : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekMasterEndConfig baseLeftRev crossedRev
          (current :: remaining) active) =
      some
        (seekMasterEndConfig baseLeftRev
          (current :: crossedRev) remaining active) := by
  cases remaining <;> cases crossedRev <;> cases active <;>
    cases baseLeftRev <;> rfl

theorem seekMasterEnd_blank_step
    (baseLeftRev masterRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekMasterEndConfig baseLeftRev masterRev [] (first :: rest)) =
      some
        { state := Control.ready
          tape := tapeAtCells
            (none :: masterRev.map some ++ none :: baseLeftRev.map some)
            (representedCells (first :: rest)) } := by
  cases rest <;> cases masterRev <;> cases baseLeftRev <;> rfl

theorem run_one_of_step
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : machine.stepConfig source = some target) :
    machine.runConfigExact? 1 source = some target := by
  rw [TuringMachine.runConfigExact?]
  rw [hstep]
  simp only [TuringMachine.runConfigExact?]

theorem run_exact_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  rw [InitialMaterializer.ExactRun.append]
  rw [hfirst]
  exact hsecond

theorem seedShift_run_exact
    (carried : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining.length + 1)
        (seedShiftConfig carried baseCells writtenRev remaining) =
      some
        (seedAtEndConfig baseCells
          (List.append writtenRev.reverse (carried :: remaining))) := by
  induction remaining generalizing carried writtenRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [seedShift_blank_step]
      rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1 + 1)
        (seedShiftConfig carried baseCells writtenRev
          (current :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seedShift_symbol_step]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih current (carried :: writtenRev)

theorem seedRewind_run_exact
    (baseCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? remainingRev.length
        (seedRewindConfig baseCells remainingRev crossed) =
      some
        (seedRewindConfig baseCells []
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil => rfl
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1)
        (seedRewindConfig baseCells (current :: more) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [seedRewind_symbol_step]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed)

def seedSteps (suffix : Word MachineCodeSymbol) : Nat :=
  1 + (suffix.length + 1) + 1 +
    (MachineCodeSymbol.header :: suffix).length + 1

theorem seed_run_exact
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (seedSteps suffix)
        (sourceConfig baseLeftRev (first :: rest) suffix) =
      some
        (selectConfig baseLeftRev (first :: rest).reverse []
          (MachineCodeSymbol.header :: suffix)) := by
  let baseCells : List (Option MachineCodeSymbol) :=
    none :: (first :: rest).reverse.map some ++
      none :: baseLeftRev.map some
  let output : Word MachineCodeSymbol :=
    MachineCodeSymbol.header :: suffix
  have h0 := run_one_of_step
    (enter_step baseLeftRev (first :: rest) suffix)
  have h1 := seedShift_run_exact MachineCodeSymbol.header
    baseCells [] suffix
  have h1' :
      machine.runConfigExact? (suffix.length + 1)
          (seedShiftConfig MachineCodeSymbol.header baseCells [] suffix) =
        some (seedAtEndConfig baseCells output) := by
    simpa [output] using h1
  have h2 :
      machine.runConfigExact? 1 (seedAtEndConfig baseCells output) =
        some (seedRewindConfig baseCells output.reverse []) := by
    exact run_one_of_step
      (seedAtEnd_step baseCells MachineCodeSymbol.header suffix)
  have h3 := seedRewind_run_exact baseCells output.reverse []
  have h3' :
      machine.runConfigExact? output.length
          (seedRewindConfig baseCells output.reverse []) =
        some (seedRewindConfig baseCells [] output) := by
    simpa [output] using h3
  have h4 :
      machine.runConfigExact? 1
          (seedRewindConfig baseCells [] output) =
        some
          (selectConfig baseLeftRev (first :: rest).reverse [] output) := by
    unfold baseCells output
    exact run_one_of_step
      (seedRewind_blank_step baseLeftRev first rest
        (MachineCodeSymbol.header :: suffix))
  have h01 := run_exact_trans h0 h1'
  have h012 := run_exact_trans h01 h2
  have h0123 := run_exact_trans h012 h3'
  have h01234 := run_exact_trans h0123 h4
  simpa [seedSteps, output, Nat.add_assoc] using h01234

theorem seekGap_run_exact
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev crossedRev remaining active :
      Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining.length + 1)
        (seekGapConfig original baseLeftRev moreRev crossedRev
          remaining active) =
      some
        (shiftConfig original original
          (none ::
            (List.append remaining.reverse crossedRev).map some ++
              some MachineCodeSymbol.header ::
                moreRev.map some ++ none :: baseLeftRev.map some)
          [] active) := by
  induction remaining generalizing crossedRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [seekGap_blank_step]
      rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1 + 1)
        (seekGapConfig original baseLeftRev moreRev crossedRev
          (current :: rest) active) = _
      rw [TuringMachine.runConfigExact?]
      rw [seekGap_symbol_step]
      simp only
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (current :: crossedRev)

theorem shift_run_exact
    (original carried : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (writtenRev remaining : Word MachineCodeSymbol) :
    machine.runConfigExact? (remaining.length + 1)
        (shiftConfig original carried baseCells writtenRev remaining) =
      some
        (atEndConfig original baseCells
          (List.append writtenRev.reverse (carried :: remaining))) := by
  induction remaining generalizing carried writtenRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [shift_blank_step]
      rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1 + 1)
        (shiftConfig original carried baseCells writtenRev
          (current :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [shift_symbol_step]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih current (carried :: writtenRev)

theorem rewind_run_exact
    (original : MachineCodeSymbol)
    (baseCells : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? remainingRev.length
        (rewindConfig original baseCells remainingRev crossed) =
      some
        (rewindConfig original baseCells []
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil => rfl
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1)
        (rewindConfig original baseCells (current :: more) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewind_symbol_step]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed)

theorem locateSource_run_exact
    (original : MachineCodeSymbol)
    (baseLeftRev moreRev remainingRev crossed output :
      Word MachineCodeSymbol)
    (hnoHeader : forall symbol : MachineCodeSymbol,
      List.Mem symbol remainingRev ->
      symbol ≠ MachineCodeSymbol.header) :
    machine.runConfigExact? remainingRev.length
        (locateSourceConfig original baseLeftRev moreRev
          remainingRev crossed output) =
      some
        (locateSourceConfig original baseLeftRev moreRev []
          (List.append remainingRev.reverse crossed) output) := by
  induction remainingRev generalizing crossed with
  | nil => rfl
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1)
        (locateSourceConfig original baseLeftRev moreRev
          (current :: more) crossed output) = _
      rw [TuringMachine.runConfigExact?]
      rw [locateSource_symbol_step original current baseLeftRev moreRev
        more crossed output (hnoHeader current (List.Mem.head more))]
      simp only
      have hmore : forall symbol : MachineCodeSymbol,
          List.Mem symbol more ->
          symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hnoHeader symbol (List.Mem.tail current hmem)
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed) hmore

theorem seekMasterEnd_run_exact
    (baseLeftRev crossedRev remaining active : Word MachineCodeSymbol) :
    machine.runConfigExact? remaining.length
        (seekMasterEndConfig baseLeftRev crossedRev remaining active) =
      some
        (seekMasterEndConfig baseLeftRev
          (List.append remaining.reverse crossedRev) [] active) := by
  induction remaining generalizing crossedRev with
  | nil => rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1)
        (seekMasterEndConfig baseLeftRev crossedRev
          (current :: rest) active) = _
      rw [TuringMachine.runConfigExact?]
      rw [seekMasterEnd_symbol_step]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossedRev)

def iterationSteps
    (processed suffix : Word MachineCodeSymbol) : Nat :=
  1 + (processed.length + 1) +
    ((List.append processed suffix).length + 1) + 1 +
    ((List.append processed suffix).length + 2) +
    (processed.length + 1)

theorem iteration_run_exact
    (current : MachineCodeSymbol)
    (baseLeftRev moreRev processed suffix : Word MachineCodeSymbol)
    (hprocessed : forall symbol : MachineCodeSymbol,
      List.Mem symbol processed ->
      symbol ≠ MachineCodeSymbol.header) :
    machine.runConfigExact? (iterationSteps processed suffix)
        (selectConfig baseLeftRev (current :: moreRev) processed suffix) =
      some
        (selectConfig baseLeftRev moreRev (current :: processed) suffix) := by
  let active := List.append processed suffix
  let baseCells : List (Option MachineCodeSymbol) :=
    none :: processed.reverse.map some ++
      some MachineCodeSymbol.header ::
        moreRev.map some ++ none :: baseLeftRev.map some
  let output := current :: active
  have h0 := run_one_of_step
    (select_symbol_step baseLeftRev moreRev processed suffix current)
  have h1 := seekGap_run_exact current baseLeftRev moreRev [] processed active
  have h1' :
      machine.runConfigExact? (processed.length + 1)
          (seekGapConfig current baseLeftRev moreRev [] processed active) =
        some (shiftConfig current current baseCells [] active) := by
    simpa [baseCells, List.map_reverse] using h1
  have h2 := shift_run_exact current current baseCells [] active
  have h2' :
      machine.runConfigExact? (active.length + 1)
          (shiftConfig current current baseCells [] active) =
        some (atEndConfig current baseCells output) := by
    simpa [output, active] using h2
  have h3 :
      machine.runConfigExact? 1 (atEndConfig current baseCells output) =
        some (rewindConfig current baseCells output.reverse []) := by
    unfold output active
    exact run_one_of_step
      (atEnd_step current baseCells current
        (List.append processed suffix))
  have h4 := rewind_run_exact current baseCells output.reverse []
  have h4' :
      machine.runConfigExact? output.length
          (rewindConfig current baseCells output.reverse []) =
        some (rewindConfig current baseCells [] output) := by
    simpa [output] using h4
  have h5 :
      machine.runConfigExact? 1
          (rewindConfig current baseCells [] output) =
        some
          (locateSourceConfig current baseLeftRev moreRev
            processed.reverse [] output) := by
    unfold baseCells output active
    exact run_one_of_step
      (rewind_blank_step current baseLeftRev moreRev processed
        (current :: List.append processed suffix))
  have hlocNoHeader : forall symbol : MachineCodeSymbol,
      List.Mem symbol processed.reverse ->
      symbol ≠ MachineCodeSymbol.header := by
    intro symbol hmem
    exact hprocessed symbol (List.mem_reverse.mp hmem)
  have h6 := locateSource_run_exact current baseLeftRev moreRev
    processed.reverse [] output hlocNoHeader
  have h6' :
      machine.runConfigExact? processed.length
          (locateSourceConfig current baseLeftRev moreRev
            processed.reverse [] output) =
        some
          (locateSourceConfig current baseLeftRev moreRev []
            processed output) := by
    simpa using h6
  have h7 :
      machine.runConfigExact? 1
          (locateSourceConfig current baseLeftRev moreRev []
            processed output) =
        some
          (selectConfig baseLeftRev moreRev (current :: processed)
            suffix) := by
    unfold output active
    exact run_one_of_step
      (locateSource_marker_step current baseLeftRev moreRev processed suffix)
  have h01 := run_exact_trans h0 h1'
  have h012 := run_exact_trans h01 h2'
  have h0123 := run_exact_trans h012 h3
  have h01234 := run_exact_trans h0123 h4'
  have h012345 := run_exact_trans h01234 h5
  have h0123456 := run_exact_trans h012345 h6'
  have h01234567 := run_exact_trans h0123456 h7
  simpa [iterationSteps, active, output, Nat.add_assoc] using h01234567

def finishSteps (master : Word MachineCodeSymbol) : Nat :=
  master.length + 2

theorem finish_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (finishSteps (first :: rest))
        (selectConfig baseLeftRev [] (first :: rest) suffix) =
      some (readyConfig baseLeftRev (first :: rest) suffix) := by
  have h0 := run_one_of_step
    (select_blank_step baseLeftRev (first :: rest) suffix)
  have h1 := seekMasterEnd_run_exact baseLeftRev []
    (first :: rest) (List.append (first :: rest) suffix)
  have h1' :
      machine.runConfigExact? (first :: rest).length
          (seekMasterEndConfig baseLeftRev [] (first :: rest)
            (List.append (first :: rest) suffix)) =
        some
          (seekMasterEndConfig baseLeftRev (first :: rest).reverse []
            (List.append (first :: rest) suffix)) := by
    simpa using h1
  have h2 :
      machine.runConfigExact? 1
          (seekMasterEndConfig baseLeftRev
            (first :: rest).reverse []
              (List.append (first :: rest) suffix)) =
        some (readyConfig baseLeftRev (first :: rest) suffix) := by
    rw [show readyConfig baseLeftRev (first :: rest) suffix =
        { state := Control.ready
          tape := tapeAtCells
            (none :: (first :: rest).reverse.map some ++
              none :: baseLeftRev.map some)
            (representedCells (List.append (first :: rest) suffix)) } by rfl]
    exact run_one_of_step
      (seekMasterEnd_blank_step baseLeftRev (first :: rest).reverse
        first (List.append rest suffix))
  have h01 := run_exact_trans h0 h1'
  have h012 := run_exact_trans h01 h2
  simpa [finishSteps, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h012

def runStepsFrom :
    Word MachineCodeSymbol -> Word MachineCodeSymbol ->
      Word MachineCodeSymbol -> Nat
  | [], processed, _suffix => finishSteps processed
  | _current :: moreRev, processed, suffix =>
      iterationSteps processed suffix +
        runStepsFrom moreRev (_current :: processed) suffix

theorem run_from_exact
    (baseLeftRev remainingRev processed suffix : Word MachineCodeSymbol)
    (hremaining : forall symbol : MachineCodeSymbol,
      List.Mem symbol remainingRev ->
      symbol ≠ MachineCodeSymbol.header)
    (hprocessed : forall symbol : MachineCodeSymbol,
      List.Mem symbol processed ->
      symbol ≠ MachineCodeSymbol.header)
    (hnonempty : remainingRev ≠ [] ∨ processed ≠ []) :
    machine.runConfigExact?
        (runStepsFrom remainingRev processed suffix)
        (selectConfig baseLeftRev remainingRev processed suffix) =
      some
        (readyConfig baseLeftRev
          (List.append remainingRev.reverse processed) suffix) := by
  induction remainingRev generalizing processed with
  | nil =>
      have hprocessedNonempty : processed ≠ [] := by
        simpa using hnonempty
      cases hprocessedWord : processed with
      | nil => contradiction
      | cons first rest =>
          simpa [runStepsFrom, hprocessedWord] using
            finish_run_exact baseLeftRev first rest suffix
  | cons current moreRev ih =>
      have hcurrent : current ≠ MachineCodeSymbol.header :=
        hremaining current (List.Mem.head moreRev)
      have hmore : forall symbol : MachineCodeSymbol,
          List.Mem symbol moreRev ->
          symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hremaining symbol (List.Mem.tail current hmem)
      have hnextProcessed : forall symbol : MachineCodeSymbol,
          List.Mem symbol (current :: processed) ->
          symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hcurrent
        · exact hprocessed symbol hmem
      have hfirst :=
        iteration_run_exact current baseLeftRev moreRev processed suffix
          hprocessed
      have hrest := ih (current :: processed) hmore hnextProcessed
        (Or.inr (by simp))
      rw [runStepsFrom]
      rw [InitialMaterializer.ExactRun.append]
      rw [hfirst]
      simpa [List.reverse_cons, List.append_assoc] using hrest

def runSteps
    (master suffix : Word MachineCodeSymbol) : Nat :=
  seedSteps suffix +
    runStepsFrom master.reverse []
      (MachineCodeSymbol.header :: suffix)

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest suffix : Word MachineCodeSymbol)
    (hnoHeader :
      transitionListParserNoHeader (first :: rest)) :
    machine.runConfigExact? (runSteps (first :: rest) suffix)
        (sourceConfig baseLeftRev (first :: rest) suffix) =
      some
        (readyConfig baseLeftRev (first :: rest)
          (MachineCodeSymbol.header :: suffix)) := by
  have h0 := seed_run_exact baseLeftRev suffix first rest
  have hremaining : forall symbol : MachineCodeSymbol,
      List.Mem symbol (first :: rest).reverse ->
      symbol ≠ MachineCodeSymbol.header := by
    intro symbol hmem
    exact hnoHeader symbol (List.mem_reverse.mp hmem)
  have h1 := run_from_exact baseLeftRev (first :: rest).reverse []
    (MachineCodeSymbol.header :: suffix)
    hremaining
    (by
      intro symbol hmem
      cases hmem)
    (Or.inl (by
      intro hnil
      have hlength := congrArg List.length hnil
      simp at hlength))
  rw [runSteps]
  rw [InitialMaterializer.ExactRun.append]
  rw [h0]
  simpa using h1

theorem raw_transition_table_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (runSteps
          (MachineDescription.encodeTransitions (first :: rest)) suffix)
        (sourceConfig baseLeftRev
          (MachineDescription.encodeTransitions (first :: rest)) suffix) =
      some
        (readyConfig baseLeftRev
          (MachineDescription.encodeTransitions (first :: rest))
          (MachineCodeSymbol.header :: suffix)) := by
  have hnonempty :
      MachineDescription.encodeTransitions (first :: rest) ≠ [] := by
    simp [MachineDescription.encodeTransitions,
      MachineDescription.encodeTransitionsAppend,
      MachineDescription.encodeTransitionAppend]
  cases htable : MachineDescription.encodeTransitions (first :: rest) with
  | nil => contradiction
  | cons firstSymbol tableRest =>
      apply run_exact baseLeftRev firstSymbol tableRest suffix
      have hraw :=
        transitionListParser_encodeTransitionsAppend_noHeader
          (first :: rest) (suffix := []) (by
            intro symbol hmem
            simp at hmem)
      change
        transitionListParserNoHeader
          (MachineDescription.encodeTransitions (first :: rest)) at hraw
      rw [htable] at hraw
      exact hraw

/-- Physical handoff used by an outer repeated-copy driver.  The inner copier
keeps `ready` terminal; after retargeting that state, one preserving left move
places the retained master back to the left of the separator and exposes the
newly copied active word as the next suffix. -/
theorem move_left_readyTape_eq_sourceTape
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (readyTape baseLeftRev (first :: rest) suffix) =
      sourceTape baseLeftRev (first :: rest)
        (List.append (first :: rest) suffix) := by
  cases rest <;> cases suffix <;> cases baseLeftRev <;>
    simp [readyTape, sourceTape, tapeAtCells, representedCells,
      Tape.move, Tape.moveLeft, List.map_append, List.append_assoc]

theorem move_left_readyConfig_tape_eq_sourceConfig_tape
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (readyConfig baseLeftRev (first :: rest) suffix).tape =
      (sourceConfig baseLeftRev (first :: rest)
        (List.append (first :: rest) suffix)).tape := by
  exact move_left_readyTape_eq_sourceTape baseLeftRev suffix first rest


end PersistentMasterCopier

end FiniteRecognizer.Interpreter.InitializerPersistentCopy

end Computability
end FoC

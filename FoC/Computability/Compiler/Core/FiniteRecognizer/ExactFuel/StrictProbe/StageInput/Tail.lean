import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Basic

/-!
# Exact-fuel stage-input tail initialization

Finite phases that initialize, rewind, and prepare the encoded nonempty input
tail before bounded insertion.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace InitialMaterializer

namespace NonemptyTailInitializer

inductive Control where
  | capture
  | seekEnd (headSymbol : MachineCodeSymbol)
  | writeDone (headSymbol : MachineCodeSymbol)
  | writeCaller (headSymbol : MachineCodeSymbol)
  | halt (headSymbol : MachineCodeSymbol)
deriving DecidableEq

namespace Control
def elems : List Control :=
  List.append [.capture] (List.append (MachineCodeSymbol.finite.elems.map Control.seekEnd)
      (List.append (MachineCodeSymbol.finite.elems.map Control.writeDone) (List.append
          (MachineCodeSymbol.finite.elems.map Control.writeCaller) (MachineCodeSymbol.finite.elems.map Control.halt))))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | capture => simp [elems]
    | seekEnd symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | writeDone symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | writeCaller symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | halt symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .capture, some headSymbol =>
      some (none, Direction.right, .seekEnd headSymbol)
  | .seekEnd headSymbol, some current =>
      some (some current, Direction.right, .seekEnd headSymbol)
  | .seekEnd headSymbol, none =>
      some (none, Direction.right, .writeDone headSymbol)
  | .writeDone headSymbol, none =>
      some (some MachineCodeSymbol.done, Direction.right, .writeCaller headSymbol)
  | .writeCaller headSymbol, none =>
      some (some Frame.callerTag, Direction.right, .halt headSymbol)
  | _, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .capture
  halt := .halt MachineCodeSymbol.header
  transition := transition
  statesFinite := Control.finite
def sourceConfig (leftRev : Word MachineCodeSymbol) (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .capture
  tape := SerializedShift.cursorTape leftRev (headSymbol :: rest)
def seekTape (leftRev crossedRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append (crossedRev.map some) (none :: leftRev.map some)
        head := none
        right := [] }
  | current :: suffix =>
      { left := List.append (crossedRev.map some) (none :: leftRev.map some)
        head := some current
        right := suffix.map some }
def seekConfig (headSymbol : MachineCodeSymbol) (leftRev crossedRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekEnd headSymbol
  tape := seekTape leftRev crossedRev rest
def writeDoneConfig (headSymbol : MachineCodeSymbol) (leftRev restRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .writeDone headSymbol
  tape :=
    { left := none :: List.append (restRev.map some) (none :: leftRev.map some)
      head := none
      right := [] }
def writeCallerConfig (headSymbol : MachineCodeSymbol) (leftRev restRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .writeCaller headSymbol
  tape :=
    { left := some MachineCodeSymbol.done :: none :: List.append (restRev.map some) (none :: leftRev.map some)
      head := none
      right := [] }
def haltConfig (headSymbol : MachineCodeSymbol) (leftRev restRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt headSymbol
  tape :=
    { left := some Frame.callerTag :: some MachineCodeSymbol.done :: none ::
          List.append (restRev.map some) (none :: leftRev.map some)
      head := none
      right := [] }
theorem capture_step (leftRev : Word MachineCodeSymbol) (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) : machine.stepConfig (sourceConfig leftRev headSymbol rest) =
      some (seekConfig headSymbol leftRev [] rest) := by
  cases rest <;> rfl
theorem seek_step (headSymbol current : MachineCodeSymbol)
    (leftRev crossedRev rest : Word MachineCodeSymbol) : machine.stepConfig
        (seekConfig headSymbol leftRev crossedRev (current :: rest)) = some
        (seekConfig headSymbol leftRev (current :: crossedRev) rest) := by
  cases rest <;> rfl
theorem seek_finish (headSymbol : MachineCodeSymbol) (leftRev restRev : Word MachineCodeSymbol) : machine.stepConfig
        (seekConfig headSymbol leftRev restRev []) = some (writeDoneConfig headSymbol leftRev restRev) := by
  rfl
theorem write_done_step (headSymbol : MachineCodeSymbol) (leftRev restRev : Word MachineCodeSymbol) : machine.stepConfig
        (writeDoneConfig headSymbol leftRev restRev) = some (writeCallerConfig headSymbol leftRev restRev) := by
  rfl
theorem write_caller_step (headSymbol : MachineCodeSymbol)
    (leftRev restRev : Word MachineCodeSymbol) : machine.stepConfig (writeCallerConfig headSymbol leftRev restRev) =
      some (haltConfig headSymbol leftRev restRev) := by
  rfl
theorem seek_run_exact (headSymbol : MachineCodeSymbol) (leftRev crossedRev rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (rest.length + 1) (seekConfig headSymbol leftRev crossedRev rest) =
      some (writeDoneConfig headSymbol leftRev (List.append rest.reverse crossedRev)) := by
  induction rest generalizing crossedRev with
  | nil =>
      exact seek_finish headSymbol leftRev crossedRev
  | cons current rest ih =>
      change machine.runConfigExact? ((rest.length + 1) + 1)
            (seekConfig headSymbol leftRev crossedRev (current :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossedRev)]
      simp [List.reverse_cons, List.append_assoc]
theorem run_exact (leftRev : Word MachineCodeSymbol) (headSymbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) : machine.runConfigExact? (rest.length + 4) (sourceConfig leftRev headSymbol rest) =
      some (haltConfig headSymbol leftRev rest.reverse) := by
  rw [show rest.length + 4 = 1 + ((rest.length + 1) + 2) by lia]
  rw [ExactRun.append]
  rw [show machine.runConfigExact? 1 (sourceConfig leftRev headSymbol rest) =
        some (seekConfig headSymbol leftRev [] rest) by
    exact capture_step leftRev headSymbol rest]
  simp only
  rw [ExactRun.append]
  rw [seek_run_exact]
  change machine.runConfigExact? 2 (writeDoneConfig headSymbol leftRev (List.append rest.reverse [])) = _
  rw [TuringMachine.runConfigExact?]
  rw [write_done_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [write_caller_step]
  simp only [TuringMachine.runConfigExact?]
  have happend : List.append rest.reverse ([] : Word MachineCodeSymbol) = rest.reverse := by
    simp
  rw [happend]
end NonemptyTailInitializer

namespace SeparatorRewind
def startTapeCells (leftContext : List (Option MachineCodeSymbol))
    (encodedRev : Word MachineCodeSymbol) : Tape MachineCodeSymbol where
  left := List.append (encodedRev.map some) (none :: leftContext)
  head := none
  right := []
def startConfigCells (leftContext : List (Option MachineCodeSymbol)) (encodedRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape := startTapeCells leftContext encodedRev
def scanTapeCells (leftContext : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := leftContext
        head := none
        right := List.append (crossed.map some) [none] }
  | current :: rest =>
      { left := List.append (rest.map some) (none :: leftContext)
        head := some current
        right := List.append (crossed.map some) [none] }
def scanConfigCells (leftContext : List (Option MachineCodeSymbol)) (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := scanTapeCells leftContext remainingRev crossed
def gateTapeCells (leftContext : List (Option MachineCodeSymbol))
    (encoded : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match encoded with
  | [] =>
      { left := none :: leftContext
        head := none
        right := [] }
  | first :: rest =>
      { left := none :: leftContext
        head := some first
        right := List.append (rest.map some) [none] }
def gateConfigCells (leftContext : List (Option MachineCodeSymbol)) (encoded : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := gateTapeCells leftContext encoded
theorem start_step_cells (leftContext : List (Option MachineCodeSymbol)) (encodedRev : Word MachineCodeSymbol) :
    machine.stepConfig (startConfigCells leftContext encodedRev) =
      some (scanConfigCells leftContext encodedRev []) := by
  cases encodedRev <;> rfl
theorem scan_step_cells (leftContext : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig (scanConfigCells leftContext (current :: remainingRev) crossed) = some
        (scanConfigCells leftContext remainingRev (current :: crossed)) := by
  cases remainingRev <;> rfl
theorem scan_finish_cells (leftContext : List (Option MachineCodeSymbol))
    (crossed : Word MachineCodeSymbol) : machine.stepConfig (scanConfigCells leftContext [] crossed) =
      some (gateConfigCells leftContext crossed) := by
  cases crossed <;> rfl
theorem scan_run_exact_cells (leftContext : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) : machine.runConfigExact? (remainingRev.length + 1)
        (scanConfigCells leftContext remainingRev crossed) = some (gateConfigCells leftContext
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish_cells leftContext crossed
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1)
            (scanConfigCells leftContext (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step_cells]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem run_exact_cells (leftContext : List (Option MachineCodeSymbol))
    (encodedRev : Word MachineCodeSymbol) : machine.runConfigExact? (encodedRev.length + 2)
        (startConfigCells leftContext encodedRev) = some (gateConfigCells leftContext encodedRev.reverse) := by
  change machine.runConfigExact? ((encodedRev.length + 1) + 1) (startConfigCells leftContext encodedRev) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step_cells]
  simp only
  simpa using scan_run_exact_cells leftContext encodedRev ([] : Word MachineCodeSymbol)
end SeparatorRewind

namespace NonemptyTailInitializer
def rewindLeftContext (leftRev restRev : Word MachineCodeSymbol) : List (Option MachineCodeSymbol) :=
  List.append (restRev.map some) (none :: leftRev.map some)
theorem separator_return_exact (leftRev restRev : Word MachineCodeSymbol) :
    SeparatorRewind.machine.runConfigExact? 4 (SeparatorRewind.startConfigCells
          (rewindLeftContext leftRev restRev) [Frame.callerTag, MachineCodeSymbol.done]) = some
        (SeparatorRewind.gateConfigCells (rewindLeftContext leftRev restRev)
          [MachineCodeSymbol.done, Frame.callerTag]) := by
  simpa using SeparatorRewind.run_exact_cells (rewindLeftContext leftRev restRev)
      ([Frame.callerTag, MachineCodeSymbol.done] : Word MachineCodeSymbol)
end NonemptyTailInitializer

namespace RightCellPrep

inductive Control where
  | start
  | separator
  | candidate
  | increment (symbol : MachineCodeSymbol)
  | locateDone (symbol : MachineCodeSymbol)
  | gate (symbol : MachineCodeSymbol)
deriving DecidableEq

namespace Control
def elems : List Control :=
  List.append [.start, .separator, .candidate] (List.append
      (MachineCodeSymbol.finite.elems.map Control.increment) (List.append
        (MachineCodeSymbol.finite.elems.map Control.locateDone) (MachineCodeSymbol.finite.elems.map Control.gate)))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | start => simp [elems]
    | separator => simp [elems]
    | candidate => simp [elems]
    | increment symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | locateDone symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | gate symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .start, cell => some (cell, Direction.left, .separator)
  | .separator, none => some (none, Direction.left, .candidate)
  | .candidate, some symbol =>
      some (none, Direction.right, .increment symbol)
  | .increment symbol, none =>
      some (some MachineCodeSymbol.tick, Direction.right, .locateDone symbol)
  | .locateDone symbol, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .locateDone symbol)
  | .locateDone symbol, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .gate symbol)
  | _, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .gate MachineCodeSymbol.header
  transition := transition
  statesFinite := Control.finite
def sourceConfig (deeperLeft : List (Option MachineCodeSymbol)) (current : MachineCodeSymbol)
    (region : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape := InsertOneWithBoundary.cursorTape (none :: some current :: deeperLeft) region
def separatorConfig (deeperLeft : List (Option MachineCodeSymbol)) (current : MachineCodeSymbol)
    (region : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .separator
  tape :=
    { left := some current :: deeperLeft
      head := none
      right := region.map some }
def candidateConfig (deeperLeft : List (Option MachineCodeSymbol)) (current : MachineCodeSymbol)
    (region : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .candidate
  tape :=
    { left := deeperLeft
      head := some current
      right := none :: region.map some }
def incrementConfig (deeperLeft : List (Option MachineCodeSymbol)) (current : MachineCodeSymbol)
    (region : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .increment current
  tape :=
    { left := none :: deeperLeft
      head := none
      right := region.map some }
def locateConfig (current : MachineCodeSymbol) (leftCells : List (Option MachineCodeSymbol))
    (rest : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .locateDone current
  tape := InsertOneWithBoundary.cursorTape leftCells rest
def gateConfig (current : MachineCodeSymbol) (leftCells : List (Option MachineCodeSymbol))
    (payload : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate current
  tape := InsertOneWithBoundary.cursorTape leftCells payload
theorem start_step_of_cons (deeperLeft : List (Option MachineCodeSymbol))
    (current first : MachineCodeSymbol) (regionRest : Word MachineCodeSymbol) :
    machine.stepConfig (sourceConfig deeperLeft current (first :: regionRest)) = some
        (separatorConfig deeperLeft current (first :: regionRest)) := by
  cases regionRest <;> rfl
theorem separator_step (deeperLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (region : Word MachineCodeSymbol) : machine.stepConfig
        (separatorConfig deeperLeft current region) = some (candidateConfig deeperLeft current region) := by
  cases region <;> rfl
theorem candidate_step (deeperLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (region : Word MachineCodeSymbol) : machine.stepConfig
        (candidateConfig deeperLeft current region) = some (incrementConfig deeperLeft current region) := by
  cases region <;> rfl
theorem increment_step_of_cons (deeperLeft : List (Option MachineCodeSymbol))
    (current first : MachineCodeSymbol) (regionRest : Word MachineCodeSymbol) :
    machine.stepConfig (incrementConfig deeperLeft current (first :: regionRest)) = some
        (locateConfig current (some MachineCodeSymbol.tick :: none :: deeperLeft) (first :: regionRest)) := by
  cases regionRest <;> rfl
theorem locate_tick_step (current : MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol)) (suffix : Word MachineCodeSymbol) :
    machine.stepConfig (locateConfig current leftCells (MachineCodeSymbol.tick :: suffix)) =
      some (locateConfig current (some MachineCodeSymbol.tick :: leftCells) suffix) := by
  cases suffix <;> rfl
theorem locate_done_step (current : MachineCodeSymbol)
    (leftCells : List (Option MachineCodeSymbol)) (payload : Word MachineCodeSymbol) :
    machine.stepConfig (locateConfig current leftCells (MachineCodeSymbol.done :: payload)) =
      some (gateConfig current (some MachineCodeSymbol.done :: leftCells) payload) := by
  cases payload <;> rfl
theorem locate_run_exact (current : MachineCodeSymbol) (count : Nat)
    (leftCells : List (Option MachineCodeSymbol)) (payload : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1) (locateConfig current leftCells
          (MachineDescription.encodeNatAppend count payload)) = some (gateConfig current
          (List.append ((MachineDescription.encodeNat count).reverse.map some) leftCells) payload) := by
  induction count generalizing leftCells with
  | zero =>
      exact locate_done_step current leftCells payload
  | succ count ih =>
      change machine.runConfigExact? ((count + 1) + 1) (locateConfig current leftCells
              (MachineCodeSymbol.tick :: MachineDescription.encodeNatAppend count payload)) = _
      rw [TuringMachine.runConfigExact?]
      rw [locate_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem prefix_run_exact_of_cons (deeperLeft : List (Option MachineCodeSymbol))
    (current first : MachineCodeSymbol) (regionRest : Word MachineCodeSymbol) :
    machine.runConfigExact? 4 (sourceConfig deeperLeft current (first :: regionRest)) = some
        (locateConfig current (some MachineCodeSymbol.tick :: none :: deeperLeft) (first :: regionRest)) := by
  change machine.runConfigExact? (3 + 1) (sourceConfig deeperLeft current (first :: regionRest)) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step_of_cons]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [separator_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [candidate_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [increment_step_of_cons]
  rfl
def payload (processed : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeOptionalCodeSymbolsPayloadAppend (processed.map some) [Frame.callerTag]
theorem region_eq_count_payload (processed : Word MachineCodeSymbol) :
    NonemptyRightRegion.region processed = MachineDescription.encodeNatAppend processed.length (payload processed) := by
  simp [NonemptyRightRegion.region, payload, encodeOptionalCodeSymbolsAppend]
theorem process_one_prep_exact (deeperLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol) :
    machine.runConfigExact? (processed.length + 5) (sourceConfig deeperLeft current
          (NonemptyRightRegion.region processed)) = some (gateConfig current (List.append
            ((MachineDescription.encodeNat processed.length).reverse.map some)
            (some MachineCodeSymbol.tick :: none :: deeperLeft)) (payload processed)) := by
  have hnonempty := NonemptyRightRegion.region_ne_nil processed
  cases hregion : NonemptyRightRegion.region processed with
  | nil =>
      contradiction
  | cons first regionRest =>
      rw [show processed.length + 5 = 4 + (processed.length + 1) by lia]
      rw [ExactRun.append]
      rw [prefix_run_exact_of_cons]
      simp only
      have hshape := region_eq_count_payload processed
      rw [hregion] at hshape
      rw [hshape]
      exact locate_run_exact current processed.length
        (some MachineCodeSymbol.tick :: none :: deeperLeft) (payload processed)
end RightCellPrep

end InitialMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

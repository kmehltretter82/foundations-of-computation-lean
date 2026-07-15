import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Input

set_option doc.verso true

/-!
# Product caller-data tail installation

Suffix-preserving nonempty and empty layout writers install the protected-frame
tail while leaving an already materialized caller frame untouched.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCallerTail

namespace NonemptyCallerTail

def sourceTape (leftRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol where
  left := leftRev.map some
  head := some headSymbol
  right := List.append (rest.map some)
    (none :: none :: none :: callerData.map some)

def sourceConfig (leftRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .capture
  tape := sourceTape leftRev headSymbol rest callerData

def seekTape (leftRev crossedRev rest callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append (crossedRev.map some)
          (none :: leftRev.map some)
        head := none
        right := none :: none :: callerData.map some }
  | current :: suffix =>
      { left := List.append (crossedRev.map some)
          (none :: leftRev.map some)
        head := some current
        right := List.append (suffix.map some)
          (none :: none :: none :: callerData.map some) }

def seekConfig (headSymbol : MachineCodeSymbol)
    (leftRev crossedRev rest callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .seekEnd headSymbol
  tape := seekTape leftRev crossedRev rest callerData

def writeDoneTape (leftRev restRev callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol where
  left := none :: List.append (restRev.map some)
    (none :: leftRev.map some)
  head := none
  right := none :: callerData.map some

def writeDoneConfig (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .writeDone headSymbol
  tape := writeDoneTape leftRev restRev callerData

def writeCallerTape (leftRev restRev callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol where
  left := some MachineCodeSymbol.done :: none ::
    List.append (restRev.map some) (none :: leftRev.map some)
  head := none
  right := callerData.map some

def writeCallerConfig (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .writeCaller headSymbol
  tape := writeCallerTape leftRev restRev callerData

def haltTape (leftRev restRev callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.move Direction.right
    (Tape.write (some Frame.callerTag)
      (writeCallerTape leftRev restRev callerData))

def haltConfig (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .halt headSymbol
  tape := haltTape leftRev restRev callerData

theorem capture_step (leftRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (sourceConfig leftRev headSymbol rest callerData) =
      some (seekConfig headSymbol leftRev [] rest callerData) := by
  cases rest <;> cases callerData <;> rfl

theorem seek_step (headSymbol current : MachineCodeSymbol)
    (leftRev crossedRev rest callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (seekConfig headSymbol leftRev crossedRev
          (current :: rest) callerData) =
      some
        (seekConfig headSymbol leftRev (current :: crossedRev)
          rest callerData) := by
  cases rest <;> cases callerData <;> rfl

theorem seek_finish (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (seekConfig headSymbol leftRev restRev [] callerData) =
      some (writeDoneConfig headSymbol leftRev restRev callerData) := by
  cases callerData <;> rfl

theorem write_done_step (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (writeDoneConfig headSymbol leftRev restRev callerData) =
      some (writeCallerConfig headSymbol leftRev restRev callerData) := by
  cases callerData <;> rfl

theorem write_caller_step (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (writeCallerConfig headSymbol leftRev restRev callerData) =
      some (haltConfig headSymbol leftRev restRev callerData) := by
  rfl

theorem seek_run_exact (headSymbol : MachineCodeSymbol)
    (leftRev crossedRev rest callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
        (rest.length + 1)
        (seekConfig headSymbol leftRev crossedRev rest callerData) =
      some
        (writeDoneConfig headSymbol leftRev
          (List.append rest.reverse crossedRev) callerData) := by
  induction rest generalizing crossedRev with
  | nil =>
      exact seek_finish headSymbol leftRev crossedRev callerData
  | cons current rest ih =>
      change
        InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
            ((rest.length + 1) + 1)
            (seekConfig headSymbol leftRev crossedRev
              (current :: rest) callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossedRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact (leftRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
        (rest.length + 4)
        (sourceConfig leftRev headSymbol rest callerData) =
      some (haltConfig headSymbol leftRev rest.reverse callerData) := by
  rw [show rest.length + 4 = 1 + ((rest.length + 1) + 2) by lia]
  rw [InitialMaterializer.ExactRun.append]
  rw [show
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact? 1
        (sourceConfig leftRev headSymbol rest callerData) =
      some (seekConfig headSymbol leftRev [] rest callerData) by
    exact capture_step leftRev headSymbol rest callerData]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [seek_run_exact]
  change
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact? 2
      (writeDoneConfig headSymbol leftRev
        (List.append rest.reverse []) callerData) = _
  rw [TuringMachine.runConfigExact?]
  rw [write_done_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [write_caller_step]
  simp only [TuringMachine.runConfigExact?]
  simp

theorem haltTape_at_callerData (leftRev restRev callerData : Word MachineCodeSymbol) :
    haltTape leftRev restRev callerData =
      { left := some Frame.callerTag :: some MachineCodeSymbol.done ::
          none :: List.append (restRev.map some)
            (none :: leftRev.map some)
        head := callerData.head?
        right := callerData.tail.map some } := by
  cases callerData <;> rfl

end NonemptyCallerTail

/-!
## Empty-input suffix writer with caller data

For an empty left input, the fixed suffix itself determines the gap width.
The existing fixed-word writer fills exactly that gap and stops on the first
caller-owned token, without reading or changing it.
-/

namespace EmptyCallerWriter

def gapTape (written rest callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := written.reverse.map some
        head := callerData.head?
        right := callerData.tail.map some }
  | _ :: tail =>
      { left := written.reverse.map some
        head := none
        right := List.append
          (List.replicate tail.length (none : Option MachineCodeSymbol))
          (callerData.map some) }

def config (word written rest callerData : Word MachineCodeSymbol)
    (hword : word = List.append written rest) :
    TuringMachine.Configuration MachineCodeSymbol (Fin (word.length + 1)) :=
  { state := InitialMaterializer.FixedWordWriter.stateAt word
      written.length (by rw [hword]; simp)
    tape := gapTape written rest callerData }

def sourceConfig (word callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Fin (word.length + 1)) :=
  config word [] word callerData (by simp)

def endpointTape (word callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  { left := word.reverse.map some
    head := callerData.head?
    right := callerData.tail.map some }

def endpointConfig (word callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Fin (word.length + 1)) :=
  { state := InitialMaterializer.FixedWordWriter.stateAt word word.length
      (by simp)
    tape := endpointTape word callerData }

theorem step (word written rest callerData : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (hword : word = List.append written (current :: rest)) :
    (InitialMaterializer.FixedWordWriter.machine word).stepConfig
        (config word written (current :: rest) callerData hword) =
      some
        (config word (List.append written [current]) rest callerData
          (by rw [hword]; simp [List.append_assoc])) := by
  subst word
  cases rest <;> cases callerData <;>
    simp [TuringMachine.stepConfig,
      InitialMaterializer.FixedWordWriter.machine,
      InitialMaterializer.FixedWordWriter.transition,
      InitialMaterializer.FixedWordWriter.stateAt,
      config, gapTape, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

theorem run_of_split (word written rest callerData : Word MachineCodeSymbol)
    (hword : word = List.append written rest) :
    (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
        rest.length (config word written rest callerData hword) =
      some (endpointConfig word callerData) := by
  induction rest generalizing written with
  | nil =>
      subst word
      simp [TuringMachine.runConfigExact?, config, endpointConfig,
        endpointTape, gapTape,
        InitialMaterializer.FixedWordWriter.stateAt]
  | cons current rest ih =>
      change
        (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
            (rest.length + 1)
            (config word written (current :: rest) callerData hword) = _
      rw [TuringMachine.runConfigExact?]
      rw [step word written rest callerData current hword]
      simp only
      have hword' :
          word = List.append (List.append written [current]) rest := by
        rw [hword]
        simp [List.append_assoc]
      exact ih (List.append written [current]) hword'

theorem run_exact (word callerData : Word MachineCodeSymbol) :
    (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
        word.length (sourceConfig word callerData) =
      some (endpointConfig word callerData) := by
  exact run_of_split word [] word callerData (by simp)

end EmptyCallerWriter

namespace EmptyCallerHeader

def callerCells (callerData : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  match callerData with
  | [] => [none]
  | _ :: _ => callerData.map some

def sourceTape (wordRev callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match callerData with
  | [] =>
      { left := wordRev.map some
        head := none
        right := [] }
  | first :: rest =>
      { left := wordRev.map some
        head := some first
        right := rest.map some }

def sourceConfig (wordRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control where
  state := .start
  tape := sourceTape wordRev callerData

def scanTape (remainingRev crossed callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) (callerCells callerData) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some) (callerCells callerData) }

def scanConfig (remainingRev crossed callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control where
  state := .scan
  tape := scanTape remainingRev crossed callerData

def gateTape (word callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := [some MachineCodeSymbol.header]
        head := callerData.head?
        right := callerData.tail.map some }
  | first :: rest =>
      { left := [some MachineCodeSymbol.header]
        head := some first
        right := List.append (rest.map some) (callerCells callerData) }

def gateConfig (word callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.PrependHeader.Control where
  state := .gate
  tape := gateTape word callerData

theorem start_step (first : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.stepConfig
        (sourceConfig (first :: rest) callerData) =
      some (scanConfig (first :: rest) [] callerData) := by
  cases rest <;> cases callerData <;> rfl

theorem scan_step (current : MachineCodeSymbol)
    (remainingRev crossed callerData : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.stepConfig
        (scanConfig (current :: remainingRev) crossed callerData) =
      some
        (scanConfig remainingRev (current :: crossed) callerData) := by
  cases remainingRev <;> cases callerData <;> rfl

theorem scan_finish (crossed callerData : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.stepConfig
        (scanConfig [] crossed callerData) =
      some (gateConfig crossed callerData) := by
  cases crossed <;> cases callerData <;> rfl

theorem scan_run_exact (remainingRev crossed callerData : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.runConfigExact?
        (remainingRev.length + 1)
        (scanConfig remainingRev crossed callerData) =
      some
        (gateConfig (List.append remainingRev.reverse crossed) callerData) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish crossed callerData
  | cons current remainingRev ih =>
      change
        InitialMaterializer.PrependHeader.machine.runConfigExact?
            ((remainingRev.length + 1) + 1)
            (scanConfig (current :: remainingRev) crossed callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact (first : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    InitialMaterializer.PrependHeader.machine.runConfigExact?
        ((first :: rest).length + 2)
        (sourceConfig (first :: rest) callerData) =
      some (gateConfig (first :: rest).reverse callerData) := by
  change
    InitialMaterializer.PrependHeader.machine.runConfigExact?
        (((first :: rest).length + 1) + 1)
        (sourceConfig (first :: rest) callerData) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step]
  simp only
  simpa using
    scan_run_exact (first :: rest) ([] : Word MachineCodeSymbol) callerData

theorem gateTape_equiv_paired_input
    (word callerData : Word MachineCodeSymbol) :
    Tape.Equiv (gateTape word callerData)
      (Tape.move Direction.right
        (Tape.input
          (MachineCodeSymbol.header :: List.append word callerData))) := by
  cases word with
  | nil =>
      cases callerData <;>
        simp [gateTape, Tape.Equiv, Tape.input,
          Tape.move, Tape.moveRight]
  | cons first rest =>
      cases callerData with
      | nil =>
          simp [gateTape, callerCells, Tape.Equiv, Tape.input,
            Tape.move, Tape.moveRight,
            FoC.Computability.dropTrailingNone_append_none]
      | cons callerFirst callerRest =>
          simp [gateTape, callerCells, Tape.Equiv, Tape.input,
            Tape.move, Tape.moveRight]

end EmptyCallerHeader


end ProductCallerTail
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC


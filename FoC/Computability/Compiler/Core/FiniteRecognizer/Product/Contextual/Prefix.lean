import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Materializer

set_option doc.verso true

/-!
# Contextual product materializer prefix

Thread a protected outer context through right-fuel parsing, nonempty tail
installation, and the separator-rewind boundary.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductContextual

namespace Parser

def tape
    (outerRev leftRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append (leftRev.map some)
          (none :: outerRev.map some)
        head := none
        right := [] }
  | first :: suffix =>
      { left := List.append (leftRev.map some)
          (none :: outerRev.map some)
        head := some first
        right := suffix.map some }

def config {stateCount : Nat}
    (control : InitialMaterializer.StageFuelParser.Control stateCount)
    (outerRev leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.StageFuelParser.Control stateCount) where
  state := control
  tape := tape outerRev leftRev rest

theorem tick_step {stateCount : Nat}
    (initialState carriedState : Fin stateCount)
    (outerRev leftRev suffix : Word MachineCodeSymbol) :
    (InitialMaterializer.StageFuelParser.machine initialState).stepConfig
        (config (.fuel carriedState) outerRev leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some (config (.fuel carriedState) outerRev
        (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem done_step {stateCount : Nat}
    (initialState carriedState : Fin stateCount)
    (outerRev leftRev suffix : Word MachineCodeSymbol) :
    (InitialMaterializer.StageFuelParser.machine initialState).stepConfig
        (config (.fuel carriedState) outerRev leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some (config (.gate carriedState) outerRev
        (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem run_from_fuel {stateCount : Nat}
    (initialState carriedState : Fin stateCount)
    (fuel : Nat) (outerRev leftRev suffix : Word MachineCodeSymbol) :
    (InitialMaterializer.StageFuelParser.machine initialState).runConfigExact?
        (fuel + 1)
        (config (.fuel carriedState) outerRev leftRev
          (MachineDescription.encodeNatAppend fuel suffix)) =
      some (config (.gate carriedState) outerRev
        (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
        suffix) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact done_step initialState carriedState outerRev leftRev suffix
  | succ fuel ih =>
      change
        (InitialMaterializer.StageFuelParser.machine initialState).runConfigExact?
            ((fuel + 1) + 1)
            (config (.fuel carriedState) outerRev leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem run_exact {stateCount : Nat}
    (initialState : Fin stateCount) (fuel : Nat)
    (outerRev input : Word MachineCodeSymbol) :
    (InitialMaterializer.StageFuelParser.machine initialState).runConfigExact?
        (fuel + 1)
        (config (.fuel initialState) outerRev []
          (MachineDescription.encodeNatAppend fuel input)) =
      some (config (.gate initialState) outerRev
        (MachineDescription.encodeNat fuel).reverse input) := by
  simpa using run_from_fuel initialState initialState fuel outerRev
    ([] : Word MachineCodeSymbol) input

end Parser

namespace Tail

def sourceTape
    (outerRev fuelRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Parser.tape outerRev fuelRev (headSymbol :: rest)

def sourceConfig
    (outerRev fuelRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .capture
  tape := sourceTape outerRev fuelRev headSymbol rest

def seekTape
    (outerRev fuelRev crossedRev rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append (crossedRev.map some)
          (none :: List.append (fuelRev.map some)
            (none :: outerRev.map some))
        head := none
        right := [] }
  | current :: suffix =>
      { left := List.append (crossedRev.map some)
          (none :: List.append (fuelRev.map some)
            (none :: outerRev.map some))
        head := some current
        right := suffix.map some }

def seekConfig
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev crossedRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .seekEnd headSymbol
  tape := seekTape outerRev fuelRev crossedRev rest

def writeDoneConfig
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .writeDone headSymbol
  tape :=
    { left := none :: List.append (restRev.map some)
        (none :: List.append (fuelRev.map some)
          (none :: outerRev.map some))
      head := none
      right := [] }

def writeCallerConfig
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .writeCaller headSymbol
  tape :=
    { left := some MachineCodeSymbol.done :: none ::
        List.append (restRev.map some)
          (none :: List.append (fuelRev.map some)
            (none :: outerRev.map some))
      head := none
      right := [] }

def haltConfig
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InitialMaterializer.NonemptyTailInitializer.Control where
  state := .halt headSymbol
  tape :=
    { left := some Frame.callerTag :: some MachineCodeSymbol.done :: none ::
        List.append (restRev.map some)
          (none :: List.append (fuelRev.map some)
            (none :: outerRev.map some))
      head := none
      right := [] }

theorem capture_step
    (outerRev fuelRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (sourceConfig outerRev fuelRev headSymbol rest) =
      some (seekConfig headSymbol outerRev fuelRev [] rest) := by
  cases rest <;> rfl

theorem seek_step
    (headSymbol current : MachineCodeSymbol)
    (outerRev fuelRev crossedRev rest : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (seekConfig headSymbol outerRev fuelRev crossedRev
          (current :: rest)) =
      some (seekConfig headSymbol outerRev fuelRev
        (current :: crossedRev) rest) := by
  cases rest <;> rfl

theorem seek_finish
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (seekConfig headSymbol outerRev fuelRev restRev []) =
      some (writeDoneConfig headSymbol outerRev fuelRev restRev) := by
  rfl

theorem write_done_step
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (writeDoneConfig headSymbol outerRev fuelRev restRev) =
      some (writeCallerConfig headSymbol outerRev fuelRev restRev) := by
  rfl

theorem write_caller_step
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.stepConfig
        (writeCallerConfig headSymbol outerRev fuelRev restRev) =
      some (haltConfig headSymbol outerRev fuelRev restRev) := by
  rfl

theorem seek_run_exact
    (headSymbol : MachineCodeSymbol)
    (outerRev fuelRev crossedRev rest : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
        (rest.length + 1)
        (seekConfig headSymbol outerRev fuelRev crossedRev rest) =
      some (writeDoneConfig headSymbol outerRev fuelRev
        (List.append rest.reverse crossedRev)) := by
  induction rest generalizing crossedRev with
  | nil =>
      exact seek_finish headSymbol outerRev fuelRev crossedRev
  | cons current rest ih =>
      change
        InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
            ((rest.length + 1) + 1)
            (seekConfig headSymbol outerRev fuelRev crossedRev
              (current :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossedRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact
    (outerRev fuelRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact?
        (rest.length + 4)
        (sourceConfig outerRev fuelRev headSymbol rest) =
      some (haltConfig headSymbol outerRev fuelRev rest.reverse) := by
  rw [show rest.length + 4 = 1 + ((rest.length + 1) + 2) by lia]
  rw [InitialMaterializer.ExactRun.append]
  rw [show
      InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact? 1
          (sourceConfig outerRev fuelRev headSymbol rest) =
        some (seekConfig headSymbol outerRev fuelRev [] rest) by
    exact capture_step outerRev fuelRev headSymbol rest]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [seek_run_exact]
  change
    InitialMaterializer.NonemptyTailInitializer.machine.runConfigExact? 2
        (writeDoneConfig headSymbol outerRev fuelRev
          (List.append rest.reverse [])) = _
  rw [TuringMachine.runConfigExact?]
  rw [write_done_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [write_caller_step]
  simp only [TuringMachine.runConfigExact?]
  simp

end Tail

def rewindLeftContext
    (outerRev fuelRev restRev : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append (restRev.map some)
    (none :: List.append (fuelRev.map some)
      (none :: outerRev.map some))

end ProductContextual
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC


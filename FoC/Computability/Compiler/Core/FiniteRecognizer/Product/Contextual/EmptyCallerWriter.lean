import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CallerTail

set_option doc.verso true

/-!
# Contextual empty-input caller writer

Run the fixed empty-input suffix writer while preserving an arbitrary
left-context word and protected caller data.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductContextual

abbrev Config (state : Type) :=
  TuringMachine.Configuration MachineCodeSymbol state

namespace EmptyCallerWriter

def gapTape (baseLeftRev written rest callerData :
    Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append (written.reverse.map some)
          (baseLeftRev.map some)
        head := callerData.head?
        right := callerData.tail.map some }
  | _ :: tail =>
      { left := List.append (written.reverse.map some)
          (baseLeftRev.map some)
        head := none
        right := List.append
          (List.replicate tail.length (none : Option MachineCodeSymbol))
          (callerData.map some) }

def config (word baseLeftRev written rest callerData :
    Word MachineCodeSymbol)
    (hword : word = List.append written rest) :
    Config (Fin (word.length + 1)) :=
  { state := InitialMaterializer.FixedWordWriter.stateAt word
      written.length (by rw [hword]; simp)
    tape := gapTape baseLeftRev written rest callerData }

def sourceConfig (word baseLeftRev callerData : Word MachineCodeSymbol) :
    Config (Fin (word.length + 1)) :=
  config word baseLeftRev [] word callerData (by simp)

def endpointConfig (word baseLeftRev callerData : Word MachineCodeSymbol) :
    Config (Fin (word.length + 1)) :=
  { state := InitialMaterializer.FixedWordWriter.stateAt word word.length
      (by simp)
    tape :=
      { left := List.append (word.reverse.map some)
          (baseLeftRev.map some)
        head := callerData.head?
        right := callerData.tail.map some } }

theorem step (word baseLeftRev written rest callerData :
    Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (hword : word = List.append written (current :: rest)) :
    (InitialMaterializer.FixedWordWriter.machine word).stepConfig
        (config word baseLeftRev written (current :: rest)
          callerData hword) =
      some
        (config word baseLeftRev
          (List.append written [current]) rest callerData
          (by rw [hword]; simp [List.append_assoc])) := by
  subst word
  cases rest <;> cases callerData <;>
    simp [TuringMachine.stepConfig,
      InitialMaterializer.FixedWordWriter.machine,
      InitialMaterializer.FixedWordWriter.transition,
      InitialMaterializer.FixedWordWriter.stateAt,
      config, gapTape, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ, List.reverse_append]

theorem run_of_split (word baseLeftRev written rest callerData :
    Word MachineCodeSymbol)
    (hword : word = List.append written rest) :
    (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
        rest.length
        (config word baseLeftRev written rest callerData hword) =
      some (endpointConfig word baseLeftRev callerData) := by
  induction rest generalizing written with
  | nil =>
      subst word
      simp [TuringMachine.runConfigExact?, config, endpointConfig, gapTape,
        InitialMaterializer.FixedWordWriter.stateAt]
  | cons current rest ih =>
      change
        (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
            (rest.length + 1)
            (config word baseLeftRev written (current :: rest)
              callerData hword) = _
      rw [TuringMachine.runConfigExact?]
      rw [step word baseLeftRev written rest callerData current hword]
      simp only
      have hword' :
          word = List.append (List.append written [current]) rest := by
        rw [hword]
        simp [List.append_assoc]
      exact ih (List.append written [current]) hword'

theorem run_exact (word baseLeftRev callerData : Word MachineCodeSymbol) :
    (InitialMaterializer.FixedWordWriter.machine word).runConfigExact?
        word.length (sourceConfig word baseLeftRev callerData) =
      some (endpointConfig word baseLeftRev callerData) := by
  exact run_of_split word baseLeftRev [] word callerData (by simp)

theorem sourceConfig_nil_eq_production
    (word callerData : Word MachineCodeSymbol) :
    sourceConfig word [] callerData =
      ProductCallerTail.EmptyCallerWriter.sourceConfig word callerData := by
  cases word <;> simp [sourceConfig, config, gapTape,
    ProductCallerTail.EmptyCallerWriter.sourceConfig,
    ProductCallerTail.EmptyCallerWriter.config,
    ProductCallerTail.EmptyCallerWriter.gapTape]

theorem endpointConfig_nil_eq_production
    (word callerData : Word MachineCodeSymbol) :
    endpointConfig word [] callerData =
    ProductCallerTail.EmptyCallerWriter.endpointConfig word callerData := by
  cases word <;> simp [endpointConfig,
    ProductCallerTail.EmptyCallerWriter.endpointConfig,
    ProductCallerTail.EmptyCallerWriter.endpointTape]

end EmptyCallerWriter

end ProductContextual
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

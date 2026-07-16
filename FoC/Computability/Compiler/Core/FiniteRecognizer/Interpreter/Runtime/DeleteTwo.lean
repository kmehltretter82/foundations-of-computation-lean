import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.EncodedList.Prepend

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimeEncodedList

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
**Two-token restaged deletion.** The bounded deletion core supports gaps of up
to ten cells. This module proves its exact run for an arbitrary pair of
physical tokens, including callers beyond the optional-field encoding.
-/

namespace DeleteTwo

def gapCell : Option MachineCodeSymbol :=
  some MachineCodeSymbol.header

theorem gap_eq_two :
    DeleteBlock.optionalGap gapCell = ⟨2, by decide⟩ := by
  rfl

def rawSourceConfig
    (leftRev : Word MachineCodeSymbol)
    (first second : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control where
  state := .erase (DeleteBlock.optionalGap gapCell)
  tape := SerializedShift.cursorTape leftRev (first :: second :: suffix)

theorem erase_exact
    (leftRev : Word MachineCodeSymbol)
    (first second : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact? 2
        (rawSourceConfig leftRev first second suffix) =
      some
        (DeleteBlock.pullConfig
          (DeleteBlock.optionalGap gapCell) leftRev suffix) := by
  cases suffix <;> rfl

theorem raw_run_exact
    (leftRev : Word MachineCodeSymbol)
    (first second : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact?
        (DeleteBlock.runSteps gapCell suffix)
        (rawSourceConfig leftRev first second suffix) =
      some
        (DeleteBlock.exitConfig gapCell
          (List.append suffix.reverse leftRev)) := by
  unfold DeleteBlock.runSteps
  change
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact?
        (2 +
          ((2 * (DeleteBlock.optionalGap gapCell).val + 1) *
            suffix.length + 1))
        (rawSourceConfig leftRev first second suffix) = _
  rw [DeleteBlock.runConfigExact?_add]
  rw [erase_exact]
  simp only
  exact DeleteBlock.pull_run_exact gapCell leftRev suffix

def sourceConfig
    (leftRev : Word MachineCodeSymbol)
    (first second : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.editConfig
    (rawSourceConfig leftRev first second suffix)

def output
    (leftRev suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append leftRev.reverse suffix

def runSteps
    (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  DeleteBlock.runSteps gapCell suffix +
    DeleteEndpointRewind.runSteps gapCell
      (List.append suffix.reverse leftRev)

theorem run_exact
    (leftRev : Word MachineCodeSymbol)
    (first second : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).runConfigExact?
        (runSteps leftRev suffix)
        (sourceConfig leftRev first second suffix) =
      some
        (DeleteRestagedMachine.rewindConfig
          (DeleteEndpointRewind.gateConfig
            (output leftRev suffix) gapCell)) := by
  have hedit := DeleteRestagedMachine.edit_run_of_eq_some gapCell _ _ _
    (raw_run_exact leftRev first second suffix)
  have hrewind := DeleteRestagedMachine.rewind_run_exact gapCell
    (List.append suffix.reverse leftRev)
  unfold runSteps sourceConfig
  rw [DeleteRestagedMachine.runConfigExact?_add]
  rw [hedit]
  simp only
  rw [hrewind]
  simp [output, List.reverse_append]

theorem target_tape_equiv_input
    (leftRev suffix : Word MachineCodeSymbol) :
    Tape.Equiv
      (DeleteRestagedMachine.rewindConfig
        (DeleteEndpointRewind.gateConfig
          (output leftRev suffix) gapCell)).tape
      (Tape.input (output leftRev suffix)) := by
  simpa [DeleteRestagedMachine.rewindConfig,
    DeleteEndpointRewind.gateConfig] using
    DeleteEndpointRewind.gateTape_equiv_input
      (output leftRev suffix) gapCell


end DeleteTwo

end FiniteRecognizer.Interpreter.RuntimeEncodedList

end Computability
end FoC

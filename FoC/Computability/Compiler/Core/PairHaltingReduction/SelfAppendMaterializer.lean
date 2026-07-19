import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.CodeAlphabetLowering
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.SelfAppendRunner

set_option doc.verso true

/-!
# Checked finite self-append materializer

This is the representation-changing middle phase of the pair-halting
reduction.  On a nonempty code-symbol word {lit}`w`, it halts with a Boolean
tape representing {lit}`w ++ w`.  Logical trailing-blank padding is transported
through the four-bit code-alphabet lowering rather than fixed to one physical
tape window.
-/

namespace FoC
namespace Computability
namespace PairHaltingReduction
namespace SelfAppendMaterializer

open Languages
open MachineDescription

private def haltRunner : TuringMachine MachineCodeSymbol Unit where
  start := ()
  halt := ()
  transition := fun _ _ => none
  statesFinite := Foundation.FiniteType.unit

def LogicalMachine : TuringMachine MachineCodeSymbol
    (SelfHaltingRecognizer.SelfAppendRunner.Control Unit) :=
  SelfHaltingRecognizer.SelfAppendRunner.machine haltRunner

def Description : MachineDescription :=
  SelfHaltingRecognizer.CodeAlphabetLowering.lowerCodeAlphabetMachineDescription
    LogicalMachine

private theorem haltRunner_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled haltRunner := by
  intro read
  rfl

theorem logicalMachine_haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled LogicalMachine :=
  SelfHaltingRecognizer.SelfAppendRunner.machine_haltingTransitionsDisabled
    haltRunner haltRunner_haltingTransitionsDisabled

theorem description_subroutineReady : Description.SubroutineReady :=
  SelfHaltingRecognizer.CodeAlphabetLowering.lowerCodeAlphabetMachineDescription_subroutineReady
    LogicalMachine

/-- The materializer's exact public contract.  The source is required to be
nonempty because the duplicator uses the first logical symbol as its initial
cursor cell. -/
theorem description_haltsFromTapeEquiv
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Description.HaltsFromTapeEquiv
      (Tape.input (encodeCodeWordAsInput (first :: rest)))
      (Tape.input (encodeCodeWordAsInput
        (List.append (first :: rest) (first :: rest)))) := by
  rcases SelfHaltingRecognizer.SelfAppendRunner.prefix_run
      haltRunner first rest with
    ⟨steps, endpoint, hrun, hstate, htape⟩
  have hcomputes : TuringMachine.Computes LogicalMachine
      (TuringMachine.initial LogicalMachine (first :: rest)) endpoint :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
  have hhalt : TuringMachine.Halted LogicalMachine endpoint := by
    change endpoint.state =
      SelfHaltingRecognizer.SelfAppendRunner.Control.run ()
    exact hstate
  have htarget :
      SelfHaltingRecognizer.CodeAlphabetLowering.RepresentsCodeTape
        (Tape.input (encodeCodeWordAsInput
          (List.append (first :: rest) (first :: rest)))) endpoint.tape :=
    SelfHaltingRecognizer.CodeAlphabetLowering.representsCodeTape_of_equiv
      (SelfHaltingRecognizer.CodeAlphabetLowering.input_representsCodeTape
        (List.append (first :: rest) (first :: rest))) htape
  exact SelfHaltingRecognizer.CodeAlphabetLowering.lowerCodeAlphabetMachineDescription_haltsFromTapeEquiv_of_computes
    LogicalMachine logicalMachine_haltingTransitionsDisabled hcomputes
      hhalt htarget

end SelfAppendMaterializer
end PairHaltingReduction
end Computability
end FoC

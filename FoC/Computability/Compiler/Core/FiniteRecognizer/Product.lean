import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode

set_option doc.verso true

/-!
# Generated product exact-fuel program boundary

Concrete finite-state construction boundary for recognizer-product exact-fuel
calls.  The public Universal/Ranges product wrapper adapts this core generated
contract to the historical code-prefix names.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer

/--
Concrete-state generated exact-fuel product runner target.
-/
def GeneratedProductExactFuelRunnerFinStateConstruction : Prop :=
  forall leftN rightN : Nat,
    forall left : TuringMachine MachineCodeSymbol (Fin leftN),
    forall right : TuringMachine MachineCodeSymbol (Fin rightN),
      exists selectedState : Type,
      exists selected : TuringMachine MachineCodeSymbol selectedState,
        ProductExactFuelRunnerSpec
          selected left right GeneratedCode.nestedStageCode

/--
Remaining concrete finite-table leaf for generated product exact-fuel calls.
It must preserve the raw input while checking the left recognizer for the
outer generated fuel and the right recognizer for the inner generated fuel.
-/
theorem generatedProductExactFuelRunnerFinStateFiniteLeaf :
    GeneratedProductExactFuelRunnerFinStateConstruction := by
  intro leftN rightN left right
  cases leftN with
  | zero =>
      exact False.elim (Fin.elim0 left.start)
  | succ _ =>
      cases rightN with
      | zero =>
          exact False.elim (Fin.elim0 right.start)
      | succ _ =>
          sorry

end FiniteRecognizer

end Computability
end FoC

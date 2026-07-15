import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Inversion
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program

set_option doc.verso true

/-!
# Product runner construction adapter

A concrete pair-prefix materializer plus the shared cyclic update kernels
assemble the public two-machine exact-fuel product specification.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductConstruction

open ProductComposition

def PairPrefixWitnesses
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) : Prop :=
  forall input leftFuel rightFuel,
    exists pairPrefix : PairPrefixWitness materializer left right
        input leftFuel rightFuel,
      pairPrefix.source =
        TuringMachine.initial materializer
          (GeneratedCode.nestedStageCode input rightFuel leftFuel)

abbrev leftKernel (leftCount : Nat) :=
  Update.Kernel.kernel leftCount

abbrev rightKernel (rightCount : Nat) :=
  Update.Kernel.kernel rightCount

theorem productExactFuelRunnerSpec_of_prefixWitnesses
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (P : PairPrefixWitnesses materializer left right) :
    ProductExactFuelRunnerSpec
      (ProductAssembly.machine materializer left right
        (leftKernel leftCount) (rightKernel rightCount))
      left right GeneratedCode.nestedStageCode := by
  intro input leftFuel rightFuel
  rcases P input leftFuel rightFuel with ⟨pairPrefix, hsource⟩
  let rightData :=
    Frame.protectedWord (Layout.initial right input rightFuel) []
  let leftW :=
    CyclicDriverWitnesses.runWitnesses left
      (leftKernel leftCount) rightData
      (Update.Runs.selectedUpdateRuns left rightData)
  let rightW :=
    CyclicDriverWitnesses.runWitnesses right
      (rightKernel rightCount) ([] : Word MachineCodeSymbol)
      (Update.Runs.selectedUpdateRuns right
        ([] : Word MachineCodeSymbol))
  have hiff := ProductInversion.haltsFrom_iff_pair
    materializer left right (leftKernel leftCount) (rightKernel rightCount)
    input leftFuel rightFuel leftW rightW pairPrefix
  rw [hsource] at hiff
  have hleftConfig :=
    StageRunner.initialFrame_semanticConfig left input leftFuel
  have hrightConfig :=
    StageRunner.initialFrame_semanticConfig right input rightFuel
  simp only [StageRunner.initialFrame] at hleftConfig hrightConfig
  rw [hleftConfig, hrightConfig] at hiff
  simpa [TuringMachine.HaltsOnInput, TuringMachine.HaltsOnInputIn,
    TuringMachine.initial,
    ProductAssembly.machine, ProductAssembly.embedMaterializer,
    TuringMachine.PhaseEmbedding.liftConfig]
    using hiff

end ProductConstruction
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC


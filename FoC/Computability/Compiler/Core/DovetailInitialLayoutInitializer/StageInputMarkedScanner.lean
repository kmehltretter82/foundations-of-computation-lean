import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.StageInputMarkedScanner.Closed

set_option doc.verso true

/-!
# Stage-input marked scanner

Public umbrella module for the stage-input marked scanner construction.
The implementation is split across submodules under this directory.
-/

namespace FoC
namespace Computability

namespace DovetailInitialLayoutInitializer

export StageInputMarkedScanner
  (StageInputMarkedScannerDescription
   stageInputMarkedScannerDescription_subroutineReady
   stageInputMarkedScannerDescription_spec)

end DovetailInitialLayoutInitializer
end Computability
end FoC

import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Compiled

set_option doc.verso true

/-!
# Initial-layout encoded rewriter

This module names the closed-handoff construction target for
{name (full := FoC.Computability.PairedRecognizerDovetailInitialLayoutCode)}`PairedRecognizerDovetailInitialLayoutCode`.
The construction is kept behind the same encoded-rewriter boundary as the
bounded runner and total-output emitter.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace InitialLayout

theorem closedHandoffCompiledSubroutine
    (accept reject : MachineDescription) :
    exists initializer : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (PairedRecognizerDovetailInitialLayoutCode accept reject)
        initializer tapeCodePrimitiveCodeWordHandoffMove := by
  exact
    DovetailInitialLayoutInitializer.pairedRecognizerDovetailInitialLayoutCode_closedHandoffCompiledSubroutine
      accept reject

end InitialLayout
end EncodedRewriters

end Computability
end FoC

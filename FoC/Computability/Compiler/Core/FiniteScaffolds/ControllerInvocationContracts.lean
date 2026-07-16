import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation

set_option doc.verso true

/-!
# Controller invocation contracts

The canonical invocation specifications and constructions live in
{module}`FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation`.
This thin module is the acceptance/import boundary for the controller
materializer and semantic-runner constructions.

Additional route structures and finite-leaf aliases are omitted because they
would only restate the canonical construction currencies.  A route wrapper
belongs here only when a checked consumer needs a genuinely different contract.
-/

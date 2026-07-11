import FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation

set_option doc.verso true

/-!
# Controller invocation contracts

The canonical invocation specifications and constructions live in
{module}`FoC.Computability.Compiler.Core.FiniteScaffolds.ControllerInvocation`.
This thin module remains as the acceptance/import boundary for the open
controller materializer and semantic-runner leaves.

The former route structures and finite-leaf aliases had no external consumers
and only restated the canonical construction currencies.  Add a route wrapper
here again only when a checked consumer needs a genuinely different contract.
-/

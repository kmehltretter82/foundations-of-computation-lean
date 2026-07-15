import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint.ExactConstruction

/-!
# Direct joined source-rest endpoint

This facade exposes the finite-machine construction that initializes the mixed
source, emits the quoted prefix, appends the live raw tail, and projects the
joined logical output back to a Boolean word, and positions the head at the
live raw-tail boundary required by the exact public consumer.
-/

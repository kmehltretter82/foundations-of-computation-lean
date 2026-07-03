import FoC.Grammars.PDAToCFG.Syntax
import FoC.Grammars.PDAToCFG.ProductionSoundness
import FoC.Grammars.PDAToCFG.ReverseDerivations
import FoC.Grammars.PDAToCFG.SummaryComputations
import FoC.Grammars.PDAToCFG.Completeness
import FoC.Grammars.PDAToCFG.Normalized

set_option doc.verso true

/-!
# PDAToCFG

This wrapper exposes the normalized PDA-to-CFG construction. The child modules
separate the generated nonterminal syntax, production soundness, reverse
derivation bookkeeping, computation summaries, completeness, and the final
normalized construction theorem.

The route is intentionally proof-heavy: the API records how a normalized PDA
stack segment is represented by a grammar nonterminal and how input is split
across the corresponding computation summary.
-/

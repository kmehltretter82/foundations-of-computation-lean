import FoC.Grammars.Parsing.LL1

set_option doc.verso true

/-!
# Parsing

Reusable parser implementations for formal grammars. The current API provides
a sound executable LL(1) parser, finite table construction and conflict
checking, and fixed-point {lit}`FIRST`/{lit}`FOLLOW` approximants in
{module}`FoC.Grammars.Parsing.LL1`.
-/

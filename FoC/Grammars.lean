import FoC.Grammars.CFG
import FoC.Grammars.CFL
import FoC.Grammars.RightRegular
import FoC.Grammars.BNF
import FoC.Grammars.ParseTree
import FoC.Grammars.PDA
import FoC.Grammars.PDANormalize
import FoC.Grammars.CFGToPDA
import FoC.Grammars.PDAToCFG
import FoC.Grammars.GeneralGrammar

set_option doc.verso true

/-!
# Grammars

## Grammar and PDA layer

The Grammars library supports Chapter 4.  It formalizes context-free grammars,
parse trees, context-free languages, pushdown automata, grammar-automaton
conversions, and the unrestricted grammars that lead into computability.

The context-free grammar core lives in {module}`FoC.Grammars.CFG`: symbols,
sentential forms, derivations, generated languages, and finite-production
vocabulary.  {module}`FoC.Grammars.CFL` packages the corresponding
context-free-language predicates, while {module}`FoC.Grammars.BNF` records the
small BNF conveniences that the book expands into ordinary productions.
{module}`FoC.Grammars.ParseTree` relates parse trees and frontiers back to
derivations.

The automata side begins with {module}`FoC.Grammars.PDA`, which models
pushdown automata by configurations with a list-valued stack.  The conversion
files, {module}`FoC.Grammars.CFGToPDA` and {module}`FoC.Grammars.PDAToCFG`,
state the standard constructions in reusable form.  {module}`FoC.Grammars.PDANormalize`
provides the finite pop-normalization layer needed by the PDA-to-CFG
construction.

Two boundary cases are kept separate.  {module}`FoC.Grammars.RightRegular`
connects right-regular grammars with finite automata, and
{module}`FoC.Grammars.GeneralGrammar` introduces unrestricted grammars for the
transition from context-free languages to recursively enumerable languages.

The chapter-facing material in {module -checked}`FoC.Book.Chapter04` uses these
modules to state the book definitions, examples, and conversion theorems in
textbook order.
-/

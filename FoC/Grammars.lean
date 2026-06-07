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

## Grammar and PDA Layer

The Grammars library supports Chapter 4.  It formalizes context-free grammars,
parse trees, context-free languages, pushdown automata, grammar-automaton
conversions, and the unrestricted grammars that lead into computability.

The central theme is that derivations, trees, and stack computations are three
ways of presenting the same finite evidence. The reusable modules keep those
presentations separate until a conversion theorem relates them.

## Grammar Semantics

The context-free grammar core lives in {module}`FoC.Grammars.CFG`: symbols,
sentential forms, derivations, generated languages, and finite-production
vocabulary.  {module}`FoC.Grammars.CFL` packages the corresponding
context-free-language predicates, while {module}`FoC.Grammars.BNF` records the
small BNF conveniences that the book expands into ordinary productions.
{module}`FoC.Grammars.ParseTree` relates parse trees and frontiers back to
derivations.

Parse trees do more than present derivations visually. They also supply the
height, frontier, subtree, and repetition machinery needed for the
context-free-language pumping argument.

## Pushdown Automata and Conversions

The automata side begins with {module}`FoC.Grammars.PDA`, which models
pushdown automata by configurations with a list-valued stack.  The conversion
files, {module}`FoC.Grammars.CFGToPDA` and {module}`FoC.Grammars.PDAToCFG`,
state the standard constructions in reusable form.  {module}`FoC.Grammars.PDANormalize`
provides the finite pop-normalization layer needed by the PDA-to-CFG
construction.

These conversion files are necessarily proof-heavy. They expose the invariants
that a textbook proof often describes informally: how a PDA stack segment
corresponds to a grammar nonterminal, how input is split across a computation,
and how a normalized pop action becomes a finite grammar production.

## Boundary Modules

Two boundary cases are kept separate.  {module}`FoC.Grammars.RightRegular`
connects right-regular grammars with finite automata, and
{module}`FoC.Grammars.GeneralGrammar` introduces unrestricted grammars for the
transition from context-free languages to recursively enumerable languages.

Right-regular grammars look backward to Chapter 3, while unrestricted grammars
look forward to Chapter 5. Keeping them outside the CFG/PDA conversion core
makes the library easier to navigate.

## Reading Route

The chapter-facing material in {module -checked}`FoC.Book.Chapter04` uses these
modules to state the book definitions, examples, and conversion theorems in
textbook order.

For a conceptual pass, read {module}`FoC.Grammars.CFG`,
{module}`FoC.Grammars.ParseTree`, and {module}`FoC.Grammars.PDA` first. Then
read the conversion modules when you want the formal content behind the
equivalence theorems.
-/

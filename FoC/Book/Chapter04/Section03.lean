import FoC.Grammars.ParseTree

namespace FoC
namespace Book
namespace Chapter04
namespace Section03

/-!
Book: Chapter 4, Section 4.3, Parsing and Parse Trees.
-/

open Languages
open Grammars

-- Book: Chapter 4, Section 4.3, every parse tree determines a derivation.
theorem parse_tree_frontier_derives {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    CFG.Derives G [s]
      (SententialForm.terminalWord (CFG.ParseTree.frontier tree)) :=
  CFG.ParseTree.derives tree

-- Book: Chapter 4, Section 4.3, parse tree for the start symbol generates a word.
theorem parse_tree_generates_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : CFG.ParseTreeGenerates G w) :
    w ∈ CFG.GeneratedLanguage G :=
  CFG.parseTree_generates_language h

-- Book: Chapter 4, Section 4.3, ambiguity via two parse trees.
def AmbiguousGrammar (G : CFG terminal nonterminal) : Prop :=
  CFG.AmbiguousByParseTrees G

inductive AmbiguousExampleTerminal where
  | a
deriving DecidableEq

inductive AmbiguousExampleNT where
  | start
  | left
  | right
deriving DecidableEq

namespace AmbiguousExampleNT

def finite : Foundation.FiniteType AmbiguousExampleNT where
  elems := [start, left, right]
  complete := by
    intro x
    cases x <;> simp

end AmbiguousExampleNT

inductive AmbiguousExampleProduces :
    AmbiguousExampleNT ->
      SententialForm AmbiguousExampleTerminal AmbiguousExampleNT -> Prop where
  | chooseLeft :
      AmbiguousExampleProduces AmbiguousExampleNT.start
        [Symbol.nonterminal AmbiguousExampleNT.left]
  | chooseRight :
      AmbiguousExampleProduces AmbiguousExampleNT.start
        [Symbol.nonterminal AmbiguousExampleNT.right]
  | leftTerminal :
      AmbiguousExampleProduces AmbiguousExampleNT.left
        [Symbol.terminal AmbiguousExampleTerminal.a]
  | rightTerminal :
      AmbiguousExampleProduces AmbiguousExampleNT.right
        [Symbol.terminal AmbiguousExampleTerminal.a]

def ambiguousExampleGrammar :
    CFG AmbiguousExampleTerminal AmbiguousExampleNT where
  start := AmbiguousExampleNT.start
  produces := AmbiguousExampleProduces
  nonterminalsFinite := AmbiguousExampleNT.finite

def ambiguousExampleLeftTree :
    CFG.ParseTree ambiguousExampleGrammar
      (Symbol.nonterminal ambiguousExampleGrammar.start) :=
  CFG.ParseTree.node AmbiguousExampleNT.start
    [Symbol.nonterminal AmbiguousExampleNT.left]
    AmbiguousExampleProduces.chooseLeft
    (CFG.ParseForest.cons
      (Symbol.nonterminal AmbiguousExampleNT.left)
      []
      (CFG.ParseTree.node AmbiguousExampleNT.left
        [Symbol.terminal AmbiguousExampleTerminal.a]
        AmbiguousExampleProduces.leftTerminal
        (CFG.ParseForest.cons
          (Symbol.terminal AmbiguousExampleTerminal.a)
          []
          (CFG.ParseTree.leaf AmbiguousExampleTerminal.a)
          CFG.ParseForest.nil))
      CFG.ParseForest.nil)

def ambiguousExampleRightTree :
    CFG.ParseTree ambiguousExampleGrammar
      (Symbol.nonterminal ambiguousExampleGrammar.start) :=
  CFG.ParseTree.node AmbiguousExampleNT.start
    [Symbol.nonterminal AmbiguousExampleNT.right]
    AmbiguousExampleProduces.chooseRight
    (CFG.ParseForest.cons
      (Symbol.nonterminal AmbiguousExampleNT.right)
      []
      (CFG.ParseTree.node AmbiguousExampleNT.right
        [Symbol.terminal AmbiguousExampleTerminal.a]
        AmbiguousExampleProduces.rightTerminal
        (CFG.ParseForest.cons
          (Symbol.terminal AmbiguousExampleTerminal.a)
          []
          (CFG.ParseTree.leaf AmbiguousExampleTerminal.a)
          CFG.ParseForest.nil))
      CFG.ParseForest.nil)

-- Book: Chapter 4, Section 4.3, an explicit ambiguous grammar witness.
theorem ambiguous_grammar_example :
    AmbiguousGrammar ambiguousExampleGrammar := by
  exists [AmbiguousExampleTerminal.a]
  exists ambiguousExampleLeftTree
  exists ambiguousExampleRightTree
  constructor
  · rfl
  constructor
  · rfl
  · intro h
    cases h

end Section03
end Chapter04
end Book
end FoC

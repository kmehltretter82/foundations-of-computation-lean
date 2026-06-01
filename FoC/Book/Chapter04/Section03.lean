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

end Section03
end Chapter04
end Book
end FoC

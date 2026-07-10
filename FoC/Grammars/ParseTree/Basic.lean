import FoC.Grammars.CFG

set_option doc.verso true

namespace FoC
namespace Grammars

open Languages

namespace CFG

/-!
# Parse-Tree Syntax and Measures

Parse trees and forests are indexed by the symbols and sentential forms they derive. This module defines their frontiers, structural measures, minimality predicate, and selected longest nonterminal paths.
-/

/-!
## Tree and forest syntax

Parse trees are indexed by the symbol they derive. A forest is the parallel
structure for a sentential form, so a node can carry one child tree per symbol
on the production right-hand side.
-/

mutual

inductive ParseTree (G : CFG terminal nonterminal) :
    Symbol terminal nonterminal -> Type where
  | leaf (a : terminal) : ParseTree G (Symbol.terminal a)
  | node (A : nonterminal) (rhs : SententialForm terminal nonterminal) :
      G.produces A rhs -> ParseForest G rhs -> ParseTree G (Symbol.nonterminal A)

inductive ParseForest (G : CFG terminal nonterminal) :
    SententialForm terminal nonterminal -> Type where
  | nil : ParseForest G []
  | cons (s : Symbol terminal nonterminal) (rest : SententialForm terminal nonterminal) :
      ParseTree G s -> ParseForest G rest -> ParseForest G (s :: rest)

end

def NonterminalSubtree (G : CFG terminal nonterminal) : Type _ :=
  Sigma (fun A : nonterminal => ParseTree G (Symbol.nonterminal A))

namespace NonterminalSubtree

def root {G : CFG terminal nonterminal} (subtree : NonterminalSubtree G) :
    nonterminal :=
  subtree.1

end NonterminalSubtree

/-!
## Frontiers

The frontier reads the terminal leaves from left to right. Forest append and
terminal-word forests provide the basic constructors used in derivation proofs.
-/

mutual

def ParseTree.frontier {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} : ParseTree G s -> Word terminal
  | ParseTree.leaf a => [a]
  | ParseTree.node _ _ _ children => ParseForest.frontier children

def ParseForest.frontier {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} :
    ParseForest G sent -> Word terminal
  | ParseForest.nil => []
  | ParseForest.cons _ _ tree rest =>
      Word.Concat (ParseTree.frontier tree) (ParseForest.frontier rest)

end

def ParseForest.append {G : CFG terminal nonterminal}
    {left right : SententialForm terminal nonterminal}
    (leftForest : ParseForest G left) (rightForest : ParseForest G right) :
    ParseForest G (left ++ right) :=
  match leftForest with
  | ParseForest.nil => rightForest
  | ParseForest.cons s rest tree forest =>
      ParseForest.cons s (rest ++ right) tree
        (ParseForest.append forest rightForest)

def ParseForest.terminalWord {G : CFG terminal nonterminal} :
    (w : Word terminal) ->
      ParseForest G (SententialForm.terminalWord (nt := nonterminal) w)
  | [] => ParseForest.nil
  | a :: rest =>
      ParseForest.cons (Symbol.terminal a) (SententialForm.terminalWord rest)
        (ParseTree.leaf a) (ParseForest.terminalWord rest)

namespace NonterminalSubtree

def frontier {G : CFG terminal nonterminal} (subtree : NonterminalSubtree G) :
    Word terminal :=
  ParseTree.frontier subtree.2

end NonterminalSubtree

/-!
## Height, size, and minimal trees

Height and node counts are the combinatorial measures used later in pumping.
Minimality chooses a smallest parse tree among those with the same frontier.
-/

mutual

def ParseTree.height {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} : ParseTree G s -> Nat
  | ParseTree.leaf _ => 0
  | ParseTree.node _ _ _ children => ParseForest.height children + 1

def ParseForest.height {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} :
    ParseForest G sent -> Nat
  | ParseForest.nil => 0
  | ParseForest.cons _ _ tree rest =>
      Nat.max (ParseTree.height tree) (ParseForest.height rest)

end

mutual

def ParseTree.nodeCount {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} : ParseTree G s -> Nat
  | ParseTree.leaf _ => 1
  | ParseTree.node _ _ _ children => ParseForest.nodeCount children + 1

def ParseForest.nodeCount {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} :
    ParseForest G sent -> Nat
  | ParseForest.nil => 0
  | ParseForest.cons _ _ tree rest =>
      ParseTree.nodeCount tree + ParseForest.nodeCount rest

end

namespace NonterminalSubtree

def nodeCount {G : CFG terminal nonterminal} (subtree : NonterminalSubtree G) :
    Nat :=
  ParseTree.nodeCount subtree.2

def height {G : CFG terminal nonterminal} (subtree : NonterminalSubtree G) :
    Nat :=
  ParseTree.height subtree.2

end NonterminalSubtree

def ParseTree.MinimalForFrontier {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) : Prop :=
  forall other : ParseTree G s,
    ParseTree.frontier other = ParseTree.frontier tree ->
      ParseTree.nodeCount tree <= ParseTree.nodeCount other

/-!
## Longest nonterminal paths

The pumping argument follows a longest path of nonterminal nodes and extracts
the corresponding nested subtrees.
-/

mutual

def ParseTree.longestNonterminalPath {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} : ParseTree G s -> List nonterminal
  | ParseTree.leaf _ => []
  | ParseTree.node A _ _ children => A :: ParseForest.longestNonterminalPath children

def ParseForest.longestNonterminalPath {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} :
    ParseForest G sent -> List nonterminal
  | ParseForest.nil => []
  | ParseForest.cons _ _ tree rest =>
      if ParseTree.height tree < ParseForest.height rest then
        ParseForest.longestNonterminalPath rest
      else
        ParseTree.longestNonterminalPath tree

end

mutual

def ParseTree.longestNonterminalSubtrees {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} :
    ParseTree G s -> List (NonterminalSubtree G)
  | ParseTree.leaf _ => []
  | ParseTree.node A rhs hprod children =>
      ⟨A, ParseTree.node A rhs hprod children⟩ ::
        ParseForest.longestNonterminalSubtrees children

def ParseForest.longestNonterminalSubtrees {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} :
    ParseForest G sent -> List (NonterminalSubtree G)
  | ParseForest.nil => []
  | ParseForest.cons _ _ tree rest =>
      if ParseTree.height tree < ParseForest.height rest then
        ParseForest.longestNonterminalSubtrees rest
      else
        ParseTree.longestNonterminalSubtrees tree

end

end CFG
end Grammars
end FoC

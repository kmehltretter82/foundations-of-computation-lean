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

-- Book: Chapter 4, Section 4.3, LL(1) parser-table vocabulary.  A table
-- entry chooses a grammar production from a nonterminal and one-symbol
-- lookahead, where `none` represents end of input.
structure LL1Parser (G : CFG terminal nonterminal) where
  table : nonterminal -> Option terminal -> Option (SententialForm terminal nonterminal)
  tableSound :
    forall A lookahead rhs, table A lookahead = some rhs -> G.produces A rhs

def LL1Parses (G : CFG terminal nonterminal) (_parser : LL1Parser G)
    (w : Word terminal) : Prop :=
  w ∈ CFG.GeneratedLanguage G

-- Book: Chapter 4, Section 4.3, LR(1) item vocabulary.  The production right
-- side is split around the dot; `lookahead = none` represents end of input.
structure LR1Item (G : CFG terminal nonterminal) where
  lhs : nonterminal
  beforeDot : SententialForm terminal nonterminal
  afterDot : SententialForm terminal nonterminal
  lookahead : Option terminal
  production :
    G.produces lhs (beforeDot ++ afterDot)

def LR1ItemComplete {G : CFG terminal nonterminal} (item : LR1Item G) : Prop :=
  item.afterDot = []

inductive ShiftReduceAction (terminal : Type u) (state : Type v)
    (nonterminal : Type w) where
  | shift : state -> ShiftReduceAction terminal state nonterminal
  | reduce : nonterminal -> SententialForm terminal nonterminal ->
      ShiftReduceAction terminal state nonterminal
  | accept : ShiftReduceAction terminal state nonterminal

structure ShiftReduceConfiguration (terminal : Type u) (state : Type v) where
  stack : List state
  unread : Word terminal

-- Book: Chapter 4, Section 4.3, LR(1)/shift-reduce parser-table vocabulary.
structure LR1Parser (G : CFG terminal nonterminal) (state : Type v) where
  startState : state
  statesFinite : Foundation.FiniteType state
  action : state -> Option terminal ->
    Option (ShiftReduceAction terminal state nonterminal)
  goto : state -> nonterminal -> Option state
  reduceSound :
    forall q lookahead A rhs,
      action q lookahead = some (ShiftReduceAction.reduce A rhs) ->
        G.produces A rhs

-- Book: Chapter 4, Section 4.3, every parse tree determines a derivation.
theorem parse_tree_frontier_derives {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    CFG.Derives G [s]
      (SententialForm.terminalWord (CFG.ParseTree.frontier tree)) :=
  CFG.ParseTree.derives tree

-- Book: Chapter 4, Section 4.3, parse-tree height vocabulary used by the
-- Section 4.5 pumping-lemma proof.
theorem parse_tree_frontier_length_bound
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    Word.Length (CFG.ParseTree.frontier tree) <=
      B ^ CFG.ParseTree.height tree :=
  CFG.ParseTree.frontier_length_le_pow hB hBound tree

-- Book: Chapter 4, Section 4.3, parse-forest height vocabulary used by the
-- Section 4.5 pumping-lemma proof.
theorem parse_forest_frontier_length_bound
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {sent : SententialForm terminal nonterminal} (forest : CFG.ParseForest G sent) :
    Word.Length (CFG.ParseForest.frontier forest) <=
      sent.length * B ^ CFG.ParseForest.height forest :=
  CFG.ParseForest.frontier_length_le_pow hB hBound forest

-- Book: Chapter 4, Section 4.3, the selected longest nonterminal path has
-- length equal to the parse-tree height.
theorem parse_tree_longest_nonterminal_path_length
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    (CFG.ParseTree.longestNonterminalPath tree).length =
      CFG.ParseTree.height tree :=
  CFG.ParseTree.longestNonterminalPath_length tree

-- Book: Chapter 4, Section 4.3, the selected longest nonterminal path through
-- a parse forest has length equal to the forest height.
theorem parse_forest_longest_nonterminal_path_length
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : CFG.ParseForest G sent) :
    (CFG.ParseForest.longestNonterminalPath forest).length =
      CFG.ParseForest.height forest :=
  CFG.ParseForest.longestNonterminalPath_length forest

-- Book: Chapter 4, Section 4.3/4.5, the selected nonterminal-subtree spine
-- has length equal to the parse-tree height.
theorem parse_tree_longest_subtree_spine_length
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    (CFG.ParseTree.longestNonterminalSubtrees tree).length =
      CFG.ParseTree.height tree :=
  CFG.ParseTree.longestNonterminalSubtrees_length tree

-- Book: Chapter 4, Section 4.3/4.5, root labels of the selected
-- nonterminal-subtree spine recover the selected nonterminal path.
theorem parse_tree_longest_subtree_spine_roots
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    (CFG.ParseTree.longestNonterminalSubtrees tree).map
        (fun subtree => CFG.NonterminalSubtree.root subtree) =
      CFG.ParseTree.longestNonterminalPath tree :=
  CFG.ParseTree.longestNonterminalSubtrees_roots tree

-- Book: Chapter 4, Section 4.3/4.5, a parse tree whose selected nonterminal
-- path is longer than the finite nonterminal list repeats a nonterminal.
theorem parse_tree_duplicate_nonterminal_on_long_path
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < CFG.ParseTree.height tree) :
    exists i j A,
      i < j ∧
      j < CFG.ParseTree.height tree ∧
      (CFG.ParseTree.longestNonterminalPath tree)[i]? = some A ∧
      (CFG.ParseTree.longestNonterminalPath tree)[j]? = some A :=
  CFG.ParseTree.exists_duplicate_nonterminal_on_long_path tree hheight

-- Book: Chapter 4, Section 4.3/4.5, duplicate labels on the selected
-- nonterminal path lift to duplicate-root selected subtrees.
theorem parse_tree_duplicate_root_subtrees_on_long_path
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < CFG.ParseTree.height tree) :
    exists i j upper lower,
      i < j ∧
      j < CFG.ParseTree.height tree ∧
      (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some upper ∧
      (CFG.ParseTree.longestNonterminalSubtrees tree)[j]? = some lower ∧
      CFG.NonterminalSubtree.root upper = CFG.NonterminalSubtree.root lower :=
  CFG.ParseTree.exists_duplicate_root_subtrees_on_long_path tree hheight

-- Book: Chapter 4, Section 4.5, an indexed selected subtree has height equal
-- to the remaining length of the selected nonterminal spine.
theorem parse_tree_selected_subtree_height_at_index
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    {i : Nat} {subtree : CFG.NonterminalSubtree G}
    (hget : (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    CFG.NonterminalSubtree.height subtree + i =
      CFG.ParseTree.height tree :=
  CFG.ParseTree.longestNonterminalSubtree_height_at_index tree hget

-- Book: Chapter 4, Section 4.5, repeated nonterminals can be chosen among the
-- bottommost |V|+1 selected nonterminal subtrees, bounding the upper subtree.
theorem parse_tree_duplicate_root_subtrees_near_bottom
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < CFG.ParseTree.height tree) :
    exists i j upper lower,
      i < j ∧
      j < CFG.ParseTree.height tree ∧
      (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some upper ∧
      (CFG.ParseTree.longestNonterminalSubtrees tree)[j]? = some lower ∧
      CFG.NonterminalSubtree.root upper = CFG.NonterminalSubtree.root lower ∧
      CFG.NonterminalSubtree.height upper <=
        G.nonterminalsFinite.elems.length + 1 :=
  CFG.ParseTree.exists_duplicate_root_subtrees_near_bottom tree hheight

-- Book: Chapter 4, Section 4.5, the upper repeated subtree has frontier
-- length bounded by the production-branching bound raised to |V|+1.
theorem parse_tree_duplicate_root_subtrees_near_bottom_frontier_bound
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < CFG.ParseTree.height tree) :
    exists i j upper lower,
      i < j ∧
      j < CFG.ParseTree.height tree ∧
      (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some upper ∧
      (CFG.ParseTree.longestNonterminalSubtrees tree)[j]? = some lower ∧
      CFG.NonterminalSubtree.root upper = CFG.NonterminalSubtree.root lower ∧
      CFG.NonterminalSubtree.height upper <=
        G.nonterminalsFinite.elems.length + 1 ∧
      Word.Length (CFG.NonterminalSubtree.frontier upper) <=
        B ^ (G.nonterminalsFinite.elems.length + 1) :=
  CFG.ParseTree.exists_duplicate_root_subtrees_near_bottom_frontier_bound
    hB hBound tree hheight

-- Book: Chapter 4, Section 4.5, a later subtree on the selected spine is on
-- the selected spine of the earlier subtree.
theorem parse_tree_later_selected_subtree_in_selected_subtree
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    {i j : Nat} {upper lower : CFG.NonterminalSubtree G}
    (hij : i <= j)
    (hupper :
      (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some upper)
    (hlower :
      (CFG.ParseTree.longestNonterminalSubtrees tree)[j]? = some lower) :
    (CFG.ParseTree.longestNonterminalSubtrees upper.2)[j - i]? = some lower :=
  CFG.ParseTree.later_selected_subtree_in_selected_subtree
    tree hij hupper hlower

-- Book: Chapter 4, Section 4.5, the repeated-root selected subtree pair gives
-- the loop derivation A =>* xAz used by the pumping construction.
theorem parse_tree_loop_derivation_from_repeated_selected_subtrees
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    {i j : Nat} {upper lower : CFG.NonterminalSubtree G}
    (hij : i <= j)
    (hupper :
      (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some upper)
    (hlower :
      (CFG.ParseTree.longestNonterminalSubtrees tree)[j]? = some lower)
    (hroot :
      CFG.NonterminalSubtree.root upper = CFG.NonterminalSubtree.root lower) :
    exists x z : Word terminal,
      CFG.NonterminalSubtree.frontier upper =
        Word.Concat x (Word.Concat (CFG.NonterminalSubtree.frontier lower) z) ∧
      CFG.Derives G
        [Symbol.nonterminal (CFG.NonterminalSubtree.root upper)]
        (SententialForm.terminalWord x ++
          [Symbol.nonterminal (CFG.NonterminalSubtree.root upper)] ++
          SententialForm.terminalWord z) :=
  CFG.ParseTree.loop_derivation_from_repeated_selected_subtrees
    tree hij hupper hlower hroot

-- Book: Chapter 4, Section 4.3/4.5, every indexed subtree on the selected
-- nonterminal spine contributes a contiguous frontier segment.
theorem parse_tree_selected_subtree_frontier_context
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    {i : Nat} {subtree : CFG.NonterminalSubtree G}
    (hget : (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    exists u v : Word terminal,
      CFG.ParseTree.frontier tree =
        Word.Concat u (Word.Concat (CFG.NonterminalSubtree.frontier subtree) v) :=
  CFG.ParseTree.longestNonterminalSubtree_get_frontier_context tree hget

-- Book: Chapter 4, Section 4.5, among parse trees with a fixed frontier and
-- root symbol, one can choose a tree of minimal node count.
theorem parse_tree_exists_minimal_for_frontier
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    exists minTree : CFG.ParseTree G s,
      CFG.ParseTree.frontier minTree = CFG.ParseTree.frontier tree ∧
      CFG.ParseTree.MinimalForFrontier minTree :=
  CFG.ParseTree.exists_minimal_for_frontier tree

-- Book: Chapter 4, Section 4.3, parse tree for the start symbol generates a word.
theorem parse_tree_generates_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : CFG.ParseTreeGenerates G w) :
    w ∈ CFG.GeneratedLanguage G :=
  CFG.parseTree_generates_language h

-- Book: Chapter 4, Section 4.3, a derivation of a terminal word determines
-- a parse forest with that frontier.
theorem parse_forest_of_derives_terminal
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Derives G sent (SententialForm.terminalWord w)) :
    exists forest : CFG.ParseForest G sent,
      CFG.ParseForest.frontier forest = w :=
  CFG.ParseForest.of_derives_terminal h

-- Book: Chapter 4, Section 4.3, generated-language membership determines a
-- parse tree rooted at the start symbol.
theorem parse_tree_of_generated_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    exists tree : CFG.ParseTree G (Symbol.nonterminal G.start),
      CFG.ParseTree.frontier tree = w :=
  CFG.ParseTree.of_generates_language h

-- Book: Chapter 4, Section 4.3, leftmost replacement in a derivation step.
def LeftmostYields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  CFG.LeftmostYields G x y

-- Book: Chapter 4, Section 4.3, rightmost replacement in a derivation step.
def RightmostYields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  CFG.RightmostYields G x y

-- Book: Chapter 4, Section 4.3, Type-valued left-derivation traces.
def LeftDerivationTrace (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Type :=
  CFG.LeftDerivationTrace G x y

-- Book: Chapter 4, Section 4.3, Type-valued right-derivation traces.
def RightDerivationTrace (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Type :=
  CFG.RightDerivationTrace G x y

-- Book: Chapter 4, Section 4.3, each parse tree has a canonical left
-- derivation trace.
def parse_tree_left_derivation_trace
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    CFG.LeftDerivationTrace G [s]
      (SententialForm.terminalWord (CFG.ParseTree.frontier tree)) :=
  CFG.ParseTree.leftDerivationTrace tree

-- Book: Chapter 4, Section 4.3, each parse forest has a canonical left
-- derivation trace.
def parse_forest_left_derivation_trace
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : CFG.ParseForest G sent) :
    CFG.LeftDerivationTrace G sent
      (SententialForm.terminalWord (CFG.ParseForest.frontier forest)) :=
  CFG.ParseForest.leftDerivationTrace forest

-- Book: Chapter 4, Section 4.3, a left derivation trace forgets to an ordinary
-- CFG derivation.
theorem left_derivation_trace_derives
    {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (trace : CFG.LeftDerivationTrace G x y) :
    CFG.Derives G x y :=
  CFG.LeftDerivationTrace.toDerives trace

-- Book: Chapter 4, Section 4.3, left derivation traces of terminal words
-- determine parse forests.
theorem parse_forest_of_left_derivation_trace
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} {w : Word terminal}
    (trace :
      CFG.LeftDerivationTrace G sent (SententialForm.terminalWord w)) :
    exists forest : CFG.ParseForest G sent,
      CFG.ParseForest.frontier forest = w :=
  CFG.leftDerivationTrace_to_parseForest_terminal trace

-- Book: Chapter 4, Section 4.3, parse trees rooted at the start symbol
-- correspond to left derivation traces of terminal words.
theorem parse_tree_left_derivation_trace_correspondence
    {G : CFG terminal nonterminal} {w : Word terminal} :
    (exists tree : CFG.ParseTree G (Symbol.nonterminal G.start),
      CFG.ParseTree.frontier tree = w) <->
    Nonempty
      (CFG.LeftDerivationTrace G [Symbol.nonterminal G.start]
        (SententialForm.terminalWord w)) :=
  CFG.parseTree_leftDerivationTrace_correspondence

-- Book: Chapter 4, Section 4.3, ambiguity via two parse trees.
def AmbiguousGrammar (G : CFG terminal nonterminal) : Prop :=
  CFG.AmbiguousByParseTrees G

-- Book: Chapter 4, Section 4.3, ambiguity via canonical left derivations is
-- equivalent to ambiguity via parse trees.
theorem ambiguous_by_parse_trees_iff_left_derivations
    (G : CFG terminal nonterminal) :
    CFG.AmbiguousByParseTrees G <-> CFG.AmbiguousByLeftDerivations G :=
  CFG.ambiguousByParseTrees_iff_leftDerivations G

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

import FoC.Grammars.Parsing.LL1

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section03

/-!
# Chapter 4, Section 4.3: Parsing and Parse Trees

This section connects parser tables, derivation traces, and parse trees in the
order used by the book. Reusable parse-tree definitions and correspondence
theorems live in {module}`FoC.Grammars.ParseTree`; the executable LL(1)
implementation lives in {module}`FoC.Grammars.Parsing.LL1`.

The book-facing material here retains the lightweight LR(1) vocabulary, the
parse-tree consequences used in the chapter narrative, and the source's
concrete {lit}`G1` and {lit}`G2` arithmetic-grammar examples.
-/

open Languages
open Grammars

/-!
## LR(1) Vocabulary

The following declarations record LR(1) items and static table shapes. They do
not define an operational shift/reduce runner or claim parser completeness.
The sound executable LL(1) API is provided by
{module}`FoC.Grammars.Parsing.LL1`.
-/

structure LR1Item (G : CFG terminal nonterminal) where
  lhs : nonterminal
  beforeDot : SententialForm terminal nonterminal
  afterDot : SententialForm terminal nonterminal
  lookahead : Option terminal
  production :
    G.produces lhs (beforeDot ++ afterDot)

inductive ShiftReduceAction (terminal : Type u) (state : Type v)
    (nonterminal : Type w) where
  | shift : state -> ShiftReduceAction terminal state nonterminal
  | reduce : nonterminal -> SententialForm terminal nonterminal ->
      ShiftReduceAction terminal state nonterminal
  | accept : ShiftReduceAction terminal state nonterminal

/--
Static LR(1) table vocabulary. This record does not yet provide an operational
shift/reduce runner or a completeness theorem.
-/
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

theorem lr1_reduce_action_is_production {G : CFG terminal nonterminal}
    {state : Type v} (parser : LR1Parser G state)
    {q : state} {lookahead : Option terminal} {A : nonterminal}
    {rhs : SententialForm terminal nonterminal}
    (h :
      parser.action q lookahead =
        some (ShiftReduceAction.reduce A rhs)) :
    G.produces A rhs :=
  parser.reduceSound q lookahead A rhs h

/-!
## Parse Trees and Frontiers

Parse trees determine derivations, and generated-language membership can be
converted back into a parse tree rooted at the start symbol. These statements
bridge the derivational and tree views of CFGs.

The frontier of a parse tree is the terminal word read from its leaves. The
bridge theorems say that parse trees and derivations are equivalent ways to
witness membership in a generated language.
-/

theorem parse_tree_frontier_derives {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    CFG.Derives G [s]
      (SententialForm.terminalWord (CFG.ParseTree.frontier tree)) :=
  CFG.ParseTree.derives tree

/-!
## Height and Repeated Nonterminals

The height bounds and repeated-subtree lemmas are the formal groundwork for
the context-free pumping lemma. They identify a repeated nonterminal on a long
path and extract the loop derivation used for pumping.

If a parse tree is taller than the number of nonterminals, some nonterminal
must repeat along a path. The later pumping argument uses the upper occurrence
and lower occurrence as a replaceable loop.
-/

theorem parse_tree_frontier_length_bound
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    Word.Length (CFG.ParseTree.frontier tree) <=
      B ^ CFG.ParseTree.height tree :=
  CFG.ParseTree.frontier_length_le_pow hB hBound tree

theorem parse_forest_frontier_length_bound
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {sent : SententialForm terminal nonterminal} (forest : CFG.ParseForest G sent) :
    Word.Length (CFG.ParseForest.frontier forest) <=
      sent.length * B ^ CFG.ParseForest.height forest :=
  CFG.ParseForest.frontier_length_le_pow hB hBound forest

theorem parse_tree_longest_nonterminal_path_length
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    (CFG.ParseTree.longestNonterminalPath tree).length =
      CFG.ParseTree.height tree :=
  CFG.ParseTree.longestNonterminalPath_length tree

theorem parse_forest_longest_nonterminal_path_length
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : CFG.ParseForest G sent) :
    (CFG.ParseForest.longestNonterminalPath forest).length =
      CFG.ParseForest.height forest :=
  CFG.ParseForest.longestNonterminalPath_length forest

theorem parse_tree_longest_subtree_spine_length
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    (CFG.ParseTree.longestNonterminalSubtrees tree).length =
      CFG.ParseTree.height tree :=
  CFG.ParseTree.longestNonterminalSubtrees_length tree

theorem parse_tree_longest_subtree_spine_roots
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    (CFG.ParseTree.longestNonterminalSubtrees tree).map
        (fun subtree => CFG.NonterminalSubtree.root subtree) =
      CFG.ParseTree.longestNonterminalPath tree :=
  CFG.ParseTree.longestNonterminalSubtrees_roots tree

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

theorem parse_tree_selected_subtree_height_at_index
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    {i : Nat} {subtree : CFG.NonterminalSubtree G}
    (hget : (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    CFG.NonterminalSubtree.height subtree + i =
      CFG.ParseTree.height tree :=
  CFG.ParseTree.longestNonterminalSubtree_height_at_index tree hget

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

theorem parse_tree_selected_subtree_frontier_context
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s)
    {i : Nat} {subtree : CFG.NonterminalSubtree G}
    (hget : (CFG.ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    exists u v : Word terminal,
      CFG.ParseTree.frontier tree =
        Word.Concat u (Word.Concat (CFG.NonterminalSubtree.frontier subtree) v) :=
  CFG.ParseTree.longestNonterminalSubtree_get_frontier_context tree hget

theorem parse_tree_exists_minimal_for_frontier
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    exists minTree : CFG.ParseTree G s,
      CFG.ParseTree.frontier minTree = CFG.ParseTree.frontier tree ∧
      CFG.ParseTree.MinimalForFrontier minTree :=
  CFG.ParseTree.exists_minimal_for_frontier tree

/-!
## Parse Trees and Generated Languages

Membership in the generated language, existence of a parse tree rooted at the
start symbol, and existence of a leftmost derivation trace are equivalent ways
to witness that a grammar generates a word.
-/

theorem parse_tree_generates_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : CFG.ParseTreeGenerates G w) :
    w ∈ CFG.GeneratedLanguage G :=
  CFG.parseTree_generates_language h

theorem parse_forest_of_derives_terminal
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} {w : Word terminal}
    (h : CFG.Derives G sent (SententialForm.terminalWord w)) :
    exists forest : CFG.ParseForest G sent,
      CFG.ParseForest.frontier forest = w :=
  CFG.ParseForest.of_derives_terminal h

theorem parse_tree_of_generated_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    exists tree : CFG.ParseTree G (Symbol.nonterminal G.start),
      CFG.ParseTree.frontier tree = w :=
  CFG.ParseTree.of_generates_language h

theorem generated_language_iff_parse_tree_exists
    {G : CFG terminal nonterminal} {w : Word terminal} :
    w ∈ CFG.GeneratedLanguage G <->
      exists tree : CFG.ParseTree G (Symbol.nonterminal G.start),
        CFG.ParseTree.frontier tree = w := by
  constructor
  · exact parse_tree_of_generated_language
  · intro h
    rcases h with ⟨tree, hfrontier⟩
    apply parse_tree_generates_language
    exact ⟨tree, hfrontier⟩

/-!
## Left Derivations and Ambiguity

A left derivation rewrites the leftmost nonterminal at every step. The book
compares left derivations as sequences of sentential forms, and calls a
grammar ambiguous when some word in its language has more than one left
derivation. Formally a left derivation is a {name}`CFG.LeftDerivationTrace`,
and its sequence of sentential forms is {name}`CFG.LeftDerivationTrace.states`;
two traces of the same word are equal exactly when their state sequences are
equal, so comparing traces is the book's comparison of derivations.

Theorem 4.5 states that parse trees and left derivations correspond one to
one. Both directions are formalized below: mapping a parse tree to its left
derivation trace is injective, and every left derivation trace of a word is
the trace of exactly one parse tree with that frontier. From this
correspondence, ambiguity by parse trees and ambiguity by left derivations
are equivalent.
-/

def parse_tree_left_derivation_trace
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : CFG.ParseTree G s) :
    CFG.LeftDerivationTrace G [s]
      (SententialForm.terminalWord (CFG.ParseTree.frontier tree)) :=
  CFG.ParseTree.leftDerivationTrace tree

def parse_forest_left_derivation_trace
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : CFG.ParseForest G sent) :
    CFG.LeftDerivationTrace G sent
      (SententialForm.terminalWord (CFG.ParseForest.frontier forest)) :=
  CFG.ParseForest.leftDerivationTrace forest

theorem left_derivation_trace_derives
    {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (trace : CFG.LeftDerivationTrace G x y) :
    CFG.Derives G x y :=
  CFG.LeftDerivationTrace.toDerives trace

theorem parse_forest_of_left_derivation_trace
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} {w : Word terminal}
    (trace :
      CFG.LeftDerivationTrace G sent (SententialForm.terminalWord w)) :
    exists forest : CFG.ParseForest G sent,
      CFG.ParseForest.frontier forest = w :=
  CFG.leftDerivationTrace_to_parseForest_terminal trace

theorem parse_tree_left_derivation_trace_correspondence
    {G : CFG terminal nonterminal} {w : Word terminal} :
    (exists tree : CFG.ParseTree G (Symbol.nonterminal G.start),
      CFG.ParseTree.frontier tree = w) <->
    Nonempty
      (CFG.LeftDerivationTrace G [Symbol.nonterminal G.start]
        (SententialForm.terminalWord w)) :=
  CFG.parseTree_leftDerivationTrace_correspondence

theorem generated_language_iff_left_derivation_trace
    {G : CFG terminal nonterminal} {w : Word terminal} :
    w ∈ CFG.GeneratedLanguage G <->
      Nonempty
        (CFG.LeftDerivationTrace G [Symbol.nonterminal G.start]
          (SententialForm.terminalWord w)) := by
  exact Iff.trans generated_language_iff_parse_tree_exists
    parse_tree_left_derivation_trace_correspondence

/-!
The next group is Theorem 4.5. Two left derivation traces of the same word
are equal exactly when they pass through the same sentential forms, sending a
parse tree to its left derivation trace is injective, and every left
derivation trace of a word comes from exactly one parse tree whose frontier
is that word.
-/

theorem left_derivation_trace_eq_of_states_eq
    {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d1 d2 : CFG.LeftDerivationTrace G x y)
    (h : d1.states = d2.states) : d1 = d2 :=
  CFG.LeftDerivationTrace.eq_of_states_eq d1 d2 h

theorem parse_tree_to_left_derivation_trace_injective
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} {w : Word terminal}
    {t1 t2 : CFG.ParseTree G s}
    {h1 : CFG.ParseTree.frontier t1 = w} {h2 : CFG.ParseTree.frontier t2 = w}
    (heq : CFG.ParseTree.leftDerivationTraceTo t1 h1 =
      CFG.ParseTree.leftDerivationTraceTo t2 h2) :
    t1 = t2 :=
  CFG.ParseTree.leftDerivationTraceTo_inj heq

theorem left_derivation_trace_unique_parse_tree
    {G : CFG terminal nonterminal} {w : Word terminal}
    (d : CFG.LeftDerivationTrace G [Symbol.nonterminal G.start]
      (SententialForm.terminalWord w)) :
    exists tree : CFG.ParseTree G (Symbol.nonterminal G.start),
      (exists hfrontier : CFG.ParseTree.frontier tree = w,
        CFG.ParseTree.leftDerivationTraceTo tree hfrontier = d) ∧
      forall (tree' : CFG.ParseTree G (Symbol.nonterminal G.start))
        (hfrontier' : CFG.ParseTree.frontier tree' = w),
        CFG.ParseTree.leftDerivationTraceTo tree' hfrontier' = d ->
          tree' = tree :=
  CFG.exists_unique_parseTree_of_leftDerivationTrace d

/-!
The book defines an ambiguous grammar by a word with more than one left
derivation; {name}`CFG.AmbiguousByLeftDerivations` states exactly that, with
two distinct traces of the same word. By Theorem 4.5 this is equivalent to the
existence of two distinct parse trees for one word, which is the working
definition used below and in later sections.
-/

def AmbiguousGrammar (G : CFG terminal nonterminal) : Prop :=
  CFG.AmbiguousByParseTrees G

def AmbiguousGrammarByLeftDerivations (G : CFG terminal nonterminal) : Prop :=
  CFG.AmbiguousByLeftDerivations G

theorem ambiguous_by_parse_trees_iff_left_derivations
    (G : CFG terminal nonterminal) :
    CFG.AmbiguousByParseTrees G <-> CFG.AmbiguousByLeftDerivations G :=
  CFG.ambiguousByParseTrees_iff_leftDerivations G

theorem ambiguous_grammar_iff_ambiguous_by_left_derivations
    (G : CFG terminal nonterminal) :
    AmbiguousGrammar G <-> AmbiguousGrammarByLeftDerivations G :=
  CFG.ambiguousByParseTrees_iff_leftDerivations G

/-!
## The Book's Ambiguous Arithmetic Grammar

The source grammar {lit}`G1` has one expression nonterminal and productions
for addition, multiplication, parentheses, and the variables {lit}`x`,
{lit}`y`, and {lit}`z`. The word {lit}`x+y*z` has two parse trees: one with
addition at the root and one with multiplication at the root.

The grammar is built directly from its displayed production list. Its finite
presentation is therefore available by construction, without a second proof
that an inductive production relation is equivalent to the same list.
-/

inductive G1Terminal where
  | x
  | y
  | z
  | plus
  | times
  | leftParen
  | rightParen
deriving DecidableEq

inductive G1NT where
  | expression
deriving DecidableEq

namespace G1NT

def finite : Foundation.FiniteType G1NT where
  elems := [expression]
  complete := by
    intro symbol
    cases symbol
    simp

end G1NT

def G1Rules : List (CFG.Production G1Terminal G1NT) :=
  [{ lhs := G1NT.expression,
     rhs := [Symbol.nonterminal G1NT.expression,
       Symbol.terminal G1Terminal.plus,
       Symbol.nonterminal G1NT.expression] },
   { lhs := G1NT.expression,
     rhs := [Symbol.nonterminal G1NT.expression,
       Symbol.terminal G1Terminal.times,
       Symbol.nonterminal G1NT.expression] },
   { lhs := G1NT.expression,
     rhs := [Symbol.terminal G1Terminal.leftParen,
       Symbol.nonterminal G1NT.expression,
       Symbol.terminal G1Terminal.rightParen] },
   { lhs := G1NT.expression, rhs := [Symbol.terminal G1Terminal.x] },
   { lhs := G1NT.expression, rhs := [Symbol.terminal G1Terminal.y] },
   { lhs := G1NT.expression, rhs := [Symbol.terminal G1Terminal.z] }]

def G1Grammar : CFG G1Terminal G1NT :=
  CFG.ProductionList.toCFG G1NT.expression G1NT.finite G1Rules

def G1Presentation : CFG.Presentation G1Grammar :=
  CFG.ProductionList.presentation G1NT.expression G1NT.finite G1Rules

theorem g1_hasFinitePresentation : CFG.HasFinitePresentation G1Grammar :=
  ⟨G1Presentation⟩

theorem g1_produces_plus : G1Grammar.produces G1NT.expression
    [Symbol.nonterminal G1NT.expression, Symbol.terminal G1Terminal.plus,
      Symbol.nonterminal G1NT.expression] := by
  simp [G1Grammar, CFG.ProductionList.toCFG, G1Rules]

theorem g1_produces_times : G1Grammar.produces G1NT.expression
    [Symbol.nonterminal G1NT.expression, Symbol.terminal G1Terminal.times,
      Symbol.nonterminal G1NT.expression] := by
  simp [G1Grammar, CFG.ProductionList.toCFG, G1Rules]

theorem g1_produces_x : G1Grammar.produces G1NT.expression
    [Symbol.terminal G1Terminal.x] := by
  simp [G1Grammar, CFG.ProductionList.toCFG, G1Rules]

theorem g1_produces_y : G1Grammar.produces G1NT.expression
    [Symbol.terminal G1Terminal.y] := by
  simp [G1Grammar, CFG.ProductionList.toCFG, G1Rules]

theorem g1_produces_z : G1Grammar.produces G1NT.expression
    [Symbol.terminal G1Terminal.z] := by
  simp [G1Grammar, CFG.ProductionList.toCFG, G1Rules]

def g1AtomTree (token : G1Terminal)
    (hprod : G1Grammar.produces G1NT.expression [Symbol.terminal token]) :
    CFG.ParseTree G1Grammar (Symbol.nonterminal G1NT.expression) :=
  CFG.ParseTree.node G1NT.expression [Symbol.terminal token] hprod
    (CFG.ParseForest.cons (Symbol.terminal token) []
      (CFG.ParseTree.leaf token) CFG.ParseForest.nil)

def g1BinaryTree (operator : G1Terminal)
    (hprod : G1Grammar.produces G1NT.expression
      [Symbol.nonterminal G1NT.expression, Symbol.terminal operator,
        Symbol.nonterminal G1NT.expression])
    (left right :
      CFG.ParseTree G1Grammar (Symbol.nonterminal G1NT.expression)) :
    CFG.ParseTree G1Grammar (Symbol.nonterminal G1NT.expression) :=
  CFG.ParseTree.node G1NT.expression
    [Symbol.nonterminal G1NT.expression, Symbol.terminal operator,
      Symbol.nonterminal G1NT.expression]
    hprod
    (CFG.ParseForest.cons (Symbol.nonterminal G1NT.expression)
      [Symbol.terminal operator, Symbol.nonterminal G1NT.expression]
      left
      (CFG.ParseForest.cons (Symbol.terminal operator)
        [Symbol.nonterminal G1NT.expression]
        (CFG.ParseTree.leaf operator)
        (CFG.ParseForest.cons (Symbol.nonterminal G1NT.expression) []
          right CFG.ParseForest.nil)))

def g1XTree := g1AtomTree G1Terminal.x g1_produces_x
def g1YTree := g1AtomTree G1Terminal.y g1_produces_y
def g1ZTree := g1AtomTree G1Terminal.z g1_produces_z

def g1PlusRootTree :=
  g1BinaryTree G1Terminal.plus g1_produces_plus g1XTree
    (g1BinaryTree G1Terminal.times g1_produces_times g1YTree g1ZTree)

def g1TimesRootTree :=
  g1BinaryTree G1Terminal.times g1_produces_times
    (g1BinaryTree G1Terminal.plus g1_produces_plus g1XTree g1YTree) g1ZTree

def g1AmbiguousWord : Word G1Terminal :=
  [G1Terminal.x, G1Terminal.plus, G1Terminal.y,
    G1Terminal.times, G1Terminal.z]

theorem g1_plusRootTree_frontier :
    CFG.ParseTree.frontier g1PlusRootTree = g1AmbiguousWord := by
  rfl

theorem g1_timesRootTree_frontier :
    CFG.ParseTree.frontier g1TimesRootTree = g1AmbiguousWord := by
  rfl

theorem g1_parse_trees_distinct : g1PlusRootTree ≠ g1TimesRootTree := by
  intro h
  cases h

theorem g1_ambiguous_on_x_plus_y_times_z :
    AmbiguousGrammar G1Grammar := by
  exact ⟨g1AmbiguousWord, g1PlusRootTree, g1TimesRootTree,
    g1_plusRootTree_frontier, g1_timesRootTree_frontier,
    g1_parse_trees_distinct⟩

theorem g1_ambiguous_by_left_derivations :
    AmbiguousGrammarByLeftDerivations G1Grammar :=
  (ambiguous_grammar_iff_ambiguous_by_left_derivations G1Grammar).mp
    g1_ambiguous_on_x_plus_y_times_z

/-!
## The Book's Precedence Grammar and an Executable Parse

The source grammar {lit}`G2` separates expressions, terms, and factors so that
multiplication binds more tightly than addition. The table below implements
the corresponding LL(1) choices. Its successful run on {lit}`x+y*z` returns a
parse tree, and the general runner theorem turns that computation into a proof
that {lit}`G2` generates the word.

This is a concrete successful-run result. It does not claim the still-missing
global completeness theorem for the generic FIRST/FOLLOW generator above.
-/

inductive G2NT where
  | expression
  | expressionTail
  | term
  | termTail
  | factor
deriving DecidableEq

namespace G2NT

def finite : Foundation.FiniteType G2NT where
  elems := [expression, expressionTail, term, termTail, factor]
  complete := by
    intro symbol
    cases symbol <;> simp

end G2NT

def g2N (A : G2NT) : Symbol G1Terminal G2NT :=
  Symbol.nonterminal A

def g2T (token : G1Terminal) : Symbol G1Terminal G2NT :=
  Symbol.terminal token

def G2Rules : List (CFG.Production G1Terminal G2NT) :=
  [{ lhs := G2NT.expression,
     rhs := [g2N G2NT.term, g2N G2NT.expressionTail] },
   { lhs := G2NT.expressionTail,
     rhs := [g2T G1Terminal.plus, g2N G2NT.term,
       g2N G2NT.expressionTail] },
   { lhs := G2NT.expressionTail, rhs := [] },
   { lhs := G2NT.term, rhs := [g2N G2NT.factor, g2N G2NT.termTail] },
   { lhs := G2NT.termTail,
     rhs := [g2T G1Terminal.times, g2N G2NT.factor, g2N G2NT.termTail] },
   { lhs := G2NT.termTail, rhs := [] },
   { lhs := G2NT.factor,
     rhs := [g2T G1Terminal.leftParen, g2N G2NT.expression,
       g2T G1Terminal.rightParen] },
   { lhs := G2NT.factor, rhs := [g2T G1Terminal.x] },
   { lhs := G2NT.factor, rhs := [g2T G1Terminal.y] },
   { lhs := G2NT.factor, rhs := [g2T G1Terminal.z] }]

def G2Grammar : CFG G1Terminal G2NT :=
  CFG.ProductionList.toCFG G2NT.expression G2NT.finite G2Rules

def G2Presentation : CFG.Presentation G2Grammar :=
  CFG.ProductionList.presentation G2NT.expression G2NT.finite G2Rules

theorem g2_hasFinitePresentation : CFG.HasFinitePresentation G2Grammar :=
  ⟨G2Presentation⟩

def G2Table : G2NT -> Option G1Terminal ->
    Option (SententialForm G1Terminal G2NT)
  | G2NT.expression, some G1Terminal.x =>
      some [g2N G2NT.term, g2N G2NT.expressionTail]
  | G2NT.expression, some G1Terminal.y =>
      some [g2N G2NT.term, g2N G2NT.expressionTail]
  | G2NT.expression, some G1Terminal.z =>
      some [g2N G2NT.term, g2N G2NT.expressionTail]
  | G2NT.expression, some G1Terminal.leftParen =>
      some [g2N G2NT.term, g2N G2NT.expressionTail]
  | G2NT.expressionTail, some G1Terminal.plus =>
      some [g2T G1Terminal.plus, g2N G2NT.term, g2N G2NT.expressionTail]
  | G2NT.expressionTail, some G1Terminal.rightParen => some []
  | G2NT.expressionTail, none => some []
  | G2NT.term, some G1Terminal.x =>
      some [g2N G2NT.factor, g2N G2NT.termTail]
  | G2NT.term, some G1Terminal.y =>
      some [g2N G2NT.factor, g2N G2NT.termTail]
  | G2NT.term, some G1Terminal.z =>
      some [g2N G2NT.factor, g2N G2NT.termTail]
  | G2NT.term, some G1Terminal.leftParen =>
      some [g2N G2NT.factor, g2N G2NT.termTail]
  | G2NT.termTail, some G1Terminal.times =>
      some [g2T G1Terminal.times, g2N G2NT.factor, g2N G2NT.termTail]
  | G2NT.termTail, some G1Terminal.plus => some []
  | G2NT.termTail, some G1Terminal.rightParen => some []
  | G2NT.termTail, none => some []
  | G2NT.factor, some G1Terminal.leftParen =>
      some [g2T G1Terminal.leftParen, g2N G2NT.expression,
        g2T G1Terminal.rightParen]
  | G2NT.factor, some G1Terminal.x => some [g2T G1Terminal.x]
  | G2NT.factor, some G1Terminal.y => some [g2T G1Terminal.y]
  | G2NT.factor, some G1Terminal.z => some [g2T G1Terminal.z]
  | _, _ => none

theorem g2_table_sound : forall (A : G2NT) (lookahead : Option G1Terminal)
    (rhs : SententialForm G1Terminal G2NT),
    G2Table A lookahead = some rhs -> G2Grammar.produces A rhs := by
  intro A lookahead rhs h
  cases A <;> cases lookahead with
  | none =>
      simp [G2Table] at h <;> subst rhs <;>
        simp [G2Grammar, CFG.ProductionList.toCFG, G2Rules]
  | some token =>
      cases token <;> simp [G2Table] at h <;> subst rhs <;>
        simp [G2Grammar, CFG.ProductionList.toCFG, G2Rules]

def G2Parser : LL1Parser G2Grammar where
  table := G2Table
  tableSound := g2_table_sound

theorem g2_parser_accepts_x_plus_y_times_z :
    (G2Parser.run 30 g1AmbiguousWord).isSome = true := by
  rfl

theorem g2_generates_x_plus_y_times_z :
    g1AmbiguousWord ∈ CFG.GeneratedLanguage G2Grammar := by
  rcases Option.isSome_iff_exists.mp g2_parser_accepts_x_plus_y_times_z with
    ⟨tree, htree⟩
  exact LL1Parser.run_sound G2Parser 30 g1AmbiguousWord tree htree

end Section03
end Chapter04
end Book
end FoC

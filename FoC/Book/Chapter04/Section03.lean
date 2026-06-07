import FoC.Grammars.ParseTree

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section03

/-!
# Chapter 4, Section 4.3: Parsing and Parse Trees

This section gives formal vocabulary for parser tables, parse trees, and
leftmost/rightmost derivation traces. The parse-tree theorems are also used
later by the context-free pumping lemma. The reusable definitions are in
{module}`FoC.Grammars.ParseTree`.

The page connects three views of parsing. A parser table describes operational
decisions, a derivation is a sequence of grammar rewrites, and a parse tree is
a structured witness explaining how a terminal word was generated.
-/

open Languages
open Grammars

/-!
## Parser Vocabulary

The LL(1), LR(1), and shift-reduce structures record the table shapes used in
the book. They are lightweight formal objects here: enough to state soundness
of table entries and to connect parsing vocabulary to grammar generation.

The formalization does not implement a full parser generator. It records the
objects and soundness obligations needed to state the book's parsing concepts
precisely, together with a fuel-bounded executable LL(1) runner whose
successful runs return parse trees.
-/

structure LL1Parser (G : CFG terminal nonterminal) where
  table : nonterminal -> Option terminal -> Option (SententialForm terminal nonterminal)
  tableSound :
    forall A lookahead rhs, table A lookahead = some rhs -> G.produces A rhs

def LL1Parses (G : CFG terminal nonterminal) (_parser : LL1Parser G)
    (w : Word terminal) : Prop :=
  w ∈ CFG.GeneratedLanguage G

theorem ll1_table_entry_is_production {G : CFG terminal nonterminal}
    (parser : LL1Parser G) {A : nonterminal} {lookahead : Option terminal}
    {rhs : SententialForm terminal nonterminal}
    (h : parser.table A lookahead = some rhs) :
    G.produces A rhs :=
  parser.tableSound A lookahead rhs h

theorem ll1_parse_sound {G : CFG terminal nonterminal}
    (parser : LL1Parser G) {w : Word terminal}
    (h : LL1Parses G parser w) :
    w ∈ CFG.GeneratedLanguage G :=
  h

/-
**Executable LL(1) runner.**  The table vocabulary above is intentionally
semantic: it records the productions licensed by a table entry.  The following
fuel-bounded runner is operational.  It consumes a word from left to right and,
on success, returns a parse tree whose frontier is exactly the consumed input.

This is the first layer of a parser-generator formalization.  Later table
generation can compute the table from FIRST/FOLLOW data; the runner below is
already executable once a table is supplied.
-/

def LL1Lookahead : Word terminal -> Option terminal
  | [] => none
  | a :: _ => some a

def LL1Parser.tableProduction {G : CFG terminal nonterminal}
    (parser : LL1Parser G) (A : nonterminal) (lookahead : Option terminal) :
    Option {rhs : SententialForm terminal nonterminal // G.produces A rhs} :=
  match htable : parser.table A lookahead with
  | none => none
  | some rhs => some ⟨rhs, parser.tableSound A lookahead rhs htable⟩

mutual

def LL1Parser.parseSymbol [DecidableEq terminal] {G : CFG terminal nonterminal}
    (parser : LL1Parser G) :
    Nat -> (s : Symbol terminal nonterminal) -> Word terminal ->
      Option (Sigma fun _rest : Word terminal => CFG.ParseTree G s)
  | 0, _, _ => none
  | _fuel + 1, Symbol.terminal a, input =>
      match input with
      | [] => none
      | b :: rest =>
          if b = a then
            some ⟨rest, CFG.ParseTree.leaf a⟩
          else
            none
  | fuel + 1, Symbol.nonterminal A, input =>
      match LL1Parser.tableProduction parser A (LL1Lookahead input) with
      | none => none
      | some ⟨rhs, hprod⟩ =>
          match LL1Parser.parseSententialForm parser fuel rhs input with
          | none => none
          | some ⟨rest, forest⟩ =>
              some ⟨rest, CFG.ParseTree.node A rhs hprod forest⟩

def LL1Parser.parseSententialForm [DecidableEq terminal]
    {G : CFG terminal nonterminal} (parser : LL1Parser G) :
    Nat -> (sent : SententialForm terminal nonterminal) -> Word terminal ->
      Option (Sigma fun _rest : Word terminal => CFG.ParseForest G sent)
  | _, [], input => some ⟨input, CFG.ParseForest.nil⟩
  | 0, _ :: _, _ => none
  | fuel + 1, s :: restSent, input =>
      match LL1Parser.parseSymbol parser fuel s input with
      | none => none
      | some ⟨middle, tree⟩ =>
          match LL1Parser.parseSententialForm parser fuel restSent middle with
          | none => none
          | some ⟨rest, forest⟩ =>
              some ⟨rest, CFG.ParseForest.cons s restSent tree forest⟩

end

def LL1Parser.run [DecidableEq terminal] {G : CFG terminal nonterminal}
    (parser : LL1Parser G) (fuel : Nat) (w : Word terminal) :
    Option (CFG.ParseTree G (Symbol.nonterminal G.start)) :=
  match LL1Parser.parseSymbol parser fuel (Symbol.nonterminal G.start) w with
  | some ⟨[], tree⟩ => some tree
  | _ => none

mutual

theorem LL1Parser.parseSymbol_frontier [DecidableEq terminal]
    {G : CFG terminal nonterminal} (parser : LL1Parser G)
    (fuel : Nat) (s : Symbol terminal nonterminal) (input : Word terminal)
    (rest : Word terminal) (tree : CFG.ParseTree G s)
    (h :
      LL1Parser.parseSymbol parser fuel s input = some ⟨rest, tree⟩) :
    input = Word.Concat (CFG.ParseTree.frontier tree) rest := by
  cases fuel with
  | zero =>
      simp [LL1Parser.parseSymbol] at h
  | succ fuel =>
      cases s with
      | terminal a =>
          cases input with
          | nil =>
              simp [LL1Parser.parseSymbol] at h
          | cons b rest =>
              by_cases hb : b = a
              · simp [LL1Parser.parseSymbol, hb] at h
                cases h
                rename_i hrest htree
                cases hrest
                cases htree
                cases hb
                rfl
              · simp [LL1Parser.parseSymbol, hb] at h
      | nonterminal A =>
          cases htable : LL1Parser.tableProduction parser A (LL1Lookahead input) with
          | none =>
              simp [LL1Parser.parseSymbol, htable] at h
          | some production =>
              rcases production with ⟨rhs, hprod⟩
              cases hparse :
                  LL1Parser.parseSententialForm parser fuel rhs input with
              | none =>
                  simp [LL1Parser.parseSymbol, htable, hparse] at h
              | some parsed =>
                  rcases parsed with ⟨rest, forest⟩
                  simp [LL1Parser.parseSymbol, htable, hparse] at h
                  cases h
                  rename_i hrest htree
                  cases hrest
                  cases htree
                  have hs :=
                    LL1Parser.parseSententialForm_frontier parser fuel rhs input
                      rest forest hparse
                  simpa [CFG.ParseTree.frontier] using hs

theorem LL1Parser.parseSententialForm_frontier [DecidableEq terminal]
    {G : CFG terminal nonterminal} (parser : LL1Parser G)
    (fuel : Nat) (sent : SententialForm terminal nonterminal)
    (input : Word terminal)
    (rest : Word terminal) (forest : CFG.ParseForest G sent)
    (h :
      LL1Parser.parseSententialForm parser fuel sent input =
        some ⟨rest, forest⟩) :
    input = Word.Concat (CFG.ParseForest.frontier forest) rest := by
  cases sent with
  | nil =>
      simp [LL1Parser.parseSententialForm] at h
      cases h
      rename_i hrest hforest
      cases hrest
      cases hforest
      rfl
  | cons s restSent =>
      cases fuel with
      | zero =>
          simp [LL1Parser.parseSententialForm] at h
      | succ fuel =>
          cases hsymbol : LL1Parser.parseSymbol parser fuel s input with
          | none =>
              simp [LL1Parser.parseSententialForm, hsymbol] at h
          | some parsedSymbol =>
              rcases parsedSymbol with ⟨middle, tree⟩
              cases hrest :
                  LL1Parser.parseSententialForm parser fuel restSent middle with
              | none =>
                  simp [LL1Parser.parseSententialForm, hsymbol, hrest] at h
              | some parsedRest =>
                  rcases parsedRest with ⟨rest, forest⟩
                  simp [LL1Parser.parseSententialForm, hsymbol, hrest] at h
                  cases h
                  rename_i hrestEq hforestEq
                  cases hrestEq
                  cases hforestEq
                  have hTree :=
                    LL1Parser.parseSymbol_frontier parser fuel s input
                      middle tree hsymbol
                  have hForest :=
                    LL1Parser.parseSententialForm_frontier parser fuel restSent
                      middle rest forest hrest
                  rw [hTree, hForest]
                  simp [CFG.ParseForest.frontier, Word.Concat,
                    List.append_assoc]

end

theorem LL1Parser.run_frontier [DecidableEq terminal]
    {G : CFG terminal nonterminal} (parser : LL1Parser G)
    (fuel : Nat) (w : Word terminal)
    (tree : CFG.ParseTree G (Symbol.nonterminal G.start))
    (h : LL1Parser.run parser fuel w = some tree) :
    CFG.ParseTree.frontier tree = w := by
  cases hparse :
      LL1Parser.parseSymbol parser fuel (Symbol.nonterminal G.start) w with
  | none =>
      simp [LL1Parser.run, hparse] at h
  | some parsed =>
      rcases parsed with ⟨rest, parsedTree⟩
      cases rest with
      | nil =>
          have hfrontier :=
            LL1Parser.parseSymbol_frontier parser fuel
              (Symbol.nonterminal G.start) w [] parsedTree hparse
          simp [LL1Parser.run, hparse] at h
          cases h
          simpa [Word.Concat] using hfrontier.symm
      | cons a restTail =>
          simp [LL1Parser.run, hparse] at h

theorem LL1Parser.run_sound [DecidableEq terminal]
    {G : CFG terminal nonterminal} (parser : LL1Parser G)
    (fuel : Nat) (w : Word terminal)
    (tree : CFG.ParseTree G (Symbol.nonterminal G.start))
    (h : LL1Parser.run parser fuel w = some tree) :
    w ∈ CFG.GeneratedLanguage G := by
  have hfrontier := LL1Parser.run_frontier parser fuel w tree h
  have hderives := CFG.ParseTree.derives tree
  simpa [CFG.GeneratedLanguage, hfrontier] using hderives

structure LL1TableEntry (terminal : Type u) (nonterminal : Type v) where
  lhs : nonterminal
  lookahead : Option terminal
  rhs : SententialForm terminal nonterminal

structure LL1ParserCode (terminal : Type u) (nonterminal : Type v) where
  entries : List (LL1TableEntry terminal nonterminal)

namespace LL1ParserCode

def lookupFrom [DecidableEq terminal] [DecidableEq nonterminal] :
    List (LL1TableEntry terminal nonterminal) -> nonterminal -> Option terminal ->
      Option (SententialForm terminal nonterminal)
  | [], _, _ => none
  | entry :: rest, A, lookahead =>
      if entry.lhs = A then
        if entry.lookahead = lookahead then
          some entry.rhs
        else
          lookupFrom rest A lookahead
      else
        lookupFrom rest A lookahead

def lookup [DecidableEq terminal] [DecidableEq nonterminal]
    (code : LL1ParserCode terminal nonterminal)
    (A : nonterminal) (lookahead : Option terminal) :
    Option (SententialForm terminal nonterminal) :=
  lookupFrom code.entries A lookahead

def toParser [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (code : LL1ParserCode terminal nonterminal)
    (hSound :
      forall A lookahead rhs,
        code.lookup A lookahead = some rhs -> G.produces A rhs) :
    LL1Parser G where
  table := code.lookup
  tableSound := hSound

def run [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (code : LL1ParserCode terminal nonterminal)
    (hSound :
      forall A lookahead rhs,
        code.lookup A lookahead = some rhs -> G.produces A rhs)
    (fuel : Nat) (w : Word terminal) :
    Option (CFG.ParseTree G (Symbol.nonterminal G.start)) :=
  LL1Parser.run (code.toParser hSound) fuel w

theorem run_sound [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (code : LL1ParserCode terminal nonterminal)
    (hSound :
      forall A lookahead rhs,
        code.lookup A lookahead = some rhs -> G.produces A rhs)
    (fuel : Nat) (w : Word terminal)
    (tree : CFG.ParseTree G (Symbol.nonterminal G.start))
    (h : code.run hSound fuel w = some tree) :
    w ∈ CFG.GeneratedLanguage G :=
  LL1Parser.run_sound (code.toParser hSound) fuel w tree h

end LL1ParserCode

structure LR1Item (G : CFG terminal nonterminal) where
  lhs : nonterminal
  beforeDot : SententialForm terminal nonterminal
  afterDot : SententialForm terminal nonterminal
  lookahead : Option terminal
  production :
    G.produces lhs (beforeDot ++ afterDot)

def LR1ItemComplete {G : CFG terminal nonterminal} (item : LR1Item G) : Prop :=
  item.afterDot = []

theorem lr1_item_complete_iff_after_dot_empty {G : CFG terminal nonterminal}
    (item : LR1Item G) :
    LR1ItemComplete item <-> item.afterDot = [] :=
  Iff.rfl

inductive ShiftReduceAction (terminal : Type u) (state : Type v)
    (nonterminal : Type w) where
  | shift : state -> ShiftReduceAction terminal state nonterminal
  | reduce : nonterminal -> SententialForm terminal nonterminal ->
      ShiftReduceAction terminal state nonterminal
  | accept : ShiftReduceAction terminal state nonterminal

structure ShiftReduceConfiguration (terminal : Type u) (state : Type v) where
  stack : List state
  unread : Word terminal

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
## Height and Repeated Nonterminals

The height bounds and repeated-subtree lemmas are the formal groundwork for
the context-free pumping lemma. They identify a repeated nonterminal on a long
path and extract the loop derivation used for pumping.

If a parse tree is taller than the number of nonterminals, some nonterminal
must repeat along a path. The later pumping argument uses the upper occurrence
and lower occurrence as a replaceable loop.
-/

def LeftmostYields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  CFG.LeftmostYields G x y

def RightmostYields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  CFG.RightmostYields G x y

def LeftDerivationTrace (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Type :=
  CFG.LeftDerivationTrace G x y

def RightDerivationTrace (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Type :=
  CFG.RightDerivationTrace G x y

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

def AmbiguousGrammar (G : CFG terminal nonterminal) : Prop :=
  CFG.AmbiguousByParseTrees G

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

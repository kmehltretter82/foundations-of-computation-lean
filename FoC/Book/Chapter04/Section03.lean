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

The formalization records the objects and soundness obligations needed to state
the book's parsing concepts precisely, together with a fuel-bounded executable
LL(1) runner whose successful runs return parse trees, a certified finite table
generator, executable conflict detection, and a fixed-point {lit}`FIRST`/
{lit}`FOLLOW` generator that automatically supplies lookahead cells.
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

This is the operational parser layer.  The finite table generator below turns
lookahead cells into executable parser code, and the fixed-point
{lit}`FIRST`/{lit}`FOLLOW` generator later in the file supplies those cells
automatically.
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

/-!
## Certified Finite Table Generation

A full textbook parser generator has two
parts: compute lookahead cells from FIRST/FOLLOW data, then turn those cells
into an executable table.  The next definitions formalize the second part.
Given a finite list of productions, each carrying its grammar-production proof,
and a computable lookahead list for each production, the generator builds
ordinary {name}`LL1ParserCode`.  The lookup theorem below is the key safety
property: every generated table hit is still a real grammar production.
-/

structure LL1ProductionEntry (G : CFG terminal nonterminal) where
  lhs : nonterminal
  rhs : SententialForm terminal nonterminal
  production : G.produces lhs rhs

namespace LL1ProductionEntry

def toTableEntry {G : CFG terminal nonterminal}
    (entry : LL1ProductionEntry G) (lookahead : Option terminal) :
    LL1TableEntry terminal nonterminal where
  lhs := entry.lhs
  lookahead := lookahead
  rhs := entry.rhs

def tableEntriesFor {G : CFG terminal nonterminal}
    (entry : LL1ProductionEntry G) :
    List (Option terminal) -> List (LL1TableEntry terminal nonterminal)
  | [] => []
  | lookahead :: rest =>
      entry.toTableEntry lookahead :: tableEntriesFor entry rest

theorem tableEntriesFor_sound {G : CFG terminal nonterminal}
    (entry : LL1ProductionEntry G)
    (lookaheads : List (Option terminal))
    {tableEntry : LL1TableEntry terminal nonterminal}
    (hmem : tableEntry ∈ tableEntriesFor entry lookaheads) :
    G.produces tableEntry.lhs tableEntry.rhs := by
  induction lookaheads with
  | nil =>
      simp [tableEntriesFor] at hmem
  | cons lookahead rest ih =>
      simp [tableEntriesFor] at hmem
      cases hmem with
      | inl hhead =>
          cases hhead
          exact entry.production
      | inr htail =>
          exact ih htail

end LL1ProductionEntry

namespace LL1TableEntry

def conflictsWith [DecidableEq terminal] [DecidableEq nonterminal]
    (left right : LL1TableEntry terminal nonterminal) : Bool :=
  if left.lhs = right.lhs then
    if left.lookahead = right.lookahead then
      if left.rhs = right.rhs then false else true
    else false
  else false

theorem conflictsWith_sound [DecidableEq terminal] [DecidableEq nonterminal]
    {left right : LL1TableEntry terminal nonterminal}
    (h : conflictsWith left right = true) :
    left.lhs = right.lhs ∧
      left.lookahead = right.lookahead ∧
      left.rhs ≠ right.rhs := by
  unfold conflictsWith at h
  by_cases hlhs : left.lhs = right.lhs
  · simp [hlhs] at h
    by_cases hlook : left.lookahead = right.lookahead
    · simp [hlook] at h
      by_cases hrhs : left.rhs = right.rhs
      · simp [hrhs] at h
      · simp [hrhs] at h
        exact ⟨hlhs, hlook, hrhs⟩
    · simp [hlook] at h
  · simp [hlhs] at h

end LL1TableEntry

namespace LL1ParserCode

def generateEntries {G : CFG terminal nonterminal}
    (lookaheads : LL1ProductionEntry G -> List (Option terminal)) :
    List (LL1ProductionEntry G) -> List (LL1TableEntry terminal nonterminal)
  | [] => []
  | production :: rest =>
      LL1ProductionEntry.tableEntriesFor production (lookaheads production) ++
        generateEntries lookaheads rest

def generated {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (lookaheads : LL1ProductionEntry G -> List (Option terminal)) :
    LL1ParserCode terminal nonterminal where
  entries := generateEntries lookaheads productions

theorem generateEntries_sound {G : CFG terminal nonterminal}
    (lookaheads : LL1ProductionEntry G -> List (Option terminal))
    (productions : List (LL1ProductionEntry G))
    {entry : LL1TableEntry terminal nonterminal}
    (hmem : entry ∈ generateEntries lookaheads productions) :
    G.produces entry.lhs entry.rhs := by
  induction productions with
  | nil =>
      simp [generateEntries] at hmem
  | cons production rest ih =>
      simp [generateEntries] at hmem
      cases hmem with
      | inl hhead =>
          exact LL1ProductionEntry.tableEntriesFor_sound production
            (lookaheads production) hhead
      | inr htail =>
          exact ih htail

theorem lookupFrom_mem [DecidableEq terminal] [DecidableEq nonterminal]
    {entries : List (LL1TableEntry terminal nonterminal)}
    {A : nonterminal} {lookahead : Option terminal}
    {rhs : SententialForm terminal nonterminal}
    (hlookup : lookupFrom entries A lookahead = some rhs) :
    exists entry,
      entry ∈ entries ∧
      entry.lhs = A ∧
      entry.lookahead = lookahead ∧
      entry.rhs = rhs := by
  induction entries with
  | nil =>
      simp [lookupFrom] at hlookup
  | cons entry rest ih =>
      by_cases hlhs : entry.lhs = A
      · by_cases hlook : entry.lookahead = lookahead
        · simp [lookupFrom, hlhs, hlook] at hlookup
          cases hlookup
          exact ⟨entry, by simp, hlhs, hlook, rfl⟩
        · simp [lookupFrom, hlhs, hlook] at hlookup
          rcases ih hlookup with ⟨found, hmem, hfoundLhs, hfoundLook, hfoundRhs⟩
          exact ⟨found, by simp [hmem], hfoundLhs, hfoundLook, hfoundRhs⟩
      · simp [lookupFrom, hlhs] at hlookup
        rcases ih hlookup with ⟨found, hmem, hfoundLhs, hfoundLook, hfoundRhs⟩
        exact ⟨found, by simp [hmem], hfoundLhs, hfoundLook, hfoundRhs⟩

theorem generated_lookup_sound [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (lookaheads : LL1ProductionEntry G -> List (Option terminal)) :
    forall A lookahead rhs,
      (generated productions lookaheads).lookup A lookahead = some rhs ->
        G.produces A rhs := by
  intro A lookahead rhs hlookup
  rcases lookupFrom_mem hlookup with
    ⟨entry, hmem, hlhs, _hlook, hrhs⟩
  have hprod := generateEntries_sound lookaheads productions hmem
  cases hlhs
  cases hrhs
  exact hprod

def generatedParser [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (lookaheads : LL1ProductionEntry G -> List (Option terminal)) :
    LL1Parser G :=
  (generated productions lookaheads).toParser
    (generated_lookup_sound productions lookaheads)

def generatedRun [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (lookaheads : LL1ProductionEntry G -> List (Option terminal))
    (fuel : Nat) (w : Word terminal) :
    Option (CFG.ParseTree G (Symbol.nonterminal G.start)) :=
  LL1Parser.run (generatedParser productions lookaheads) fuel w

theorem generatedRun_sound [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (lookaheads : LL1ProductionEntry G -> List (Option terminal))
    (fuel : Nat) (w : Word terminal)
    (tree : CFG.ParseTree G (Symbol.nonterminal G.start))
    (h : generatedRun productions lookaheads fuel w = some tree) :
    w ∈ CFG.GeneratedLanguage G :=
  LL1Parser.run_sound (generatedParser productions lookaheads) fuel w tree h

def entryConflictsWithAny [DecidableEq terminal] [DecidableEq nonterminal]
    (entry : LL1TableEntry terminal nonterminal) :
    List (LL1TableEntry terminal nonterminal) -> Bool
  | [] => false
  | other :: rest =>
      LL1TableEntry.conflictsWith entry other ||
        entryConflictsWithAny entry rest

def hasConflictFrom [DecidableEq terminal] [DecidableEq nonterminal] :
    List (LL1TableEntry terminal nonterminal) -> Bool
  | [] => false
  | entry :: rest =>
      entryConflictsWithAny entry rest || hasConflictFrom rest

def hasConflict [DecidableEq terminal] [DecidableEq nonterminal]
    (code : LL1ParserCode terminal nonterminal) : Bool :=
  hasConflictFrom code.entries

def ConflictFree (code : LL1ParserCode terminal nonterminal) : Prop :=
  forall left right,
    left ∈ code.entries -> right ∈ code.entries ->
      left.lhs = right.lhs -> left.lookahead = right.lookahead ->
        left.rhs = right.rhs

theorem entryConflictsWithAny_sound
    [DecidableEq terminal] [DecidableEq nonterminal]
    (entry : LL1TableEntry terminal nonterminal)
    (entries : List (LL1TableEntry terminal nonterminal))
    (h : entryConflictsWithAny entry entries = true) :
    exists other,
      other ∈ entries ∧ LL1TableEntry.conflictsWith entry other = true := by
  induction entries with
  | nil =>
      simp [entryConflictsWithAny] at h
  | cons other rest ih =>
      simp [entryConflictsWithAny] at h
      cases h with
      | inl hhead =>
          exact ⟨other, by simp, hhead⟩
      | inr htail =>
          rcases ih htail with ⟨found, hmem, hconflict⟩
          exact ⟨found, by simp [hmem], hconflict⟩

theorem hasConflictFrom_sound
    [DecidableEq terminal] [DecidableEq nonterminal]
    (entries : List (LL1TableEntry terminal nonterminal))
    (h : hasConflictFrom entries = true) :
    exists left right,
      left ∈ entries ∧ right ∈ entries ∧
        LL1TableEntry.conflictsWith left right = true := by
  induction entries with
  | nil =>
      simp [hasConflictFrom] at h
  | cons entry rest ih =>
      simp [hasConflictFrom] at h
      cases h with
      | inl hhead =>
          rcases entryConflictsWithAny_sound entry rest hhead with
            ⟨right, hright, hconflict⟩
          exact ⟨entry, right, by simp, by simp [hright], hconflict⟩
      | inr htail =>
          rcases ih htail with ⟨left, right, hleft, hright, hconflict⟩
          exact ⟨left, right, by simp [hleft], by simp [hright], hconflict⟩

theorem hasConflict_sound [DecidableEq terminal] [DecidableEq nonterminal]
    (code : LL1ParserCode terminal nonterminal)
    (h : hasConflict code = true) :
    exists left right,
      left ∈ code.entries ∧ right ∈ code.entries ∧
        left.lhs = right.lhs ∧
        left.lookahead = right.lookahead ∧
        left.rhs ≠ right.rhs := by
  rcases hasConflictFrom_sound code.entries h with
    ⟨left, right, hleft, hright, hconflict⟩
  have hdata := LL1TableEntry.conflictsWith_sound hconflict
  exact ⟨left, right, hleft, hright, hdata⟩

theorem conflictsWith_false_same_keys
    [DecidableEq terminal] [DecidableEq nonterminal]
    {left right : LL1TableEntry terminal nonterminal}
    (h : LL1TableEntry.conflictsWith left right = false)
    (hlhs : left.lhs = right.lhs)
    (hlook : left.lookahead = right.lookahead) :
    left.rhs = right.rhs := by
  unfold LL1TableEntry.conflictsWith at h
  simp [hlhs, hlook] at h
  by_cases hrhs : left.rhs = right.rhs
  · exact hrhs
  · simp [hrhs] at h

theorem entryConflictsWithAny_false_same_keys
    [DecidableEq terminal] [DecidableEq nonterminal]
    (entry : LL1TableEntry terminal nonterminal)
    (entries : List (LL1TableEntry terminal nonterminal))
    (h : entryConflictsWithAny entry entries = false)
    {other : LL1TableEntry terminal nonterminal}
    (hmem : other ∈ entries)
    (hlhs : entry.lhs = other.lhs)
    (hlook : entry.lookahead = other.lookahead) :
    entry.rhs = other.rhs := by
  induction entries with
  | nil =>
      cases hmem
  | cons head rest ih =>
      simp [entryConflictsWithAny] at h
      rcases h with ⟨hhead, hrest⟩
      cases hmem with
      | head =>
          exact conflictsWith_false_same_keys hhead hlhs hlook
      | tail _ htail =>
          exact ih hrest htail

theorem hasConflictFrom_false_conflictFree
    [DecidableEq terminal] [DecidableEq nonterminal]
    (entries : List (LL1TableEntry terminal nonterminal))
    (h : hasConflictFrom entries = false) :
    forall left right,
      left ∈ entries -> right ∈ entries ->
        left.lhs = right.lhs -> left.lookahead = right.lookahead ->
          left.rhs = right.rhs := by
  induction entries with
  | nil =>
      intro left right hleft
      cases hleft
  | cons head rest ih =>
      simp [hasConflictFrom] at h
      rcases h with ⟨hhead, htail⟩
      intro left right hleft hright hlhs hlook
      cases hleft with
      | head =>
          cases hright with
          | head =>
              rfl
          | tail _ hrightTail =>
              exact entryConflictsWithAny_false_same_keys
                head rest hhead hrightTail hlhs hlook
      | tail _ hleftTail =>
          cases hright with
          | head =>
              exact (entryConflictsWithAny_false_same_keys
                head rest hhead hleftTail hlhs.symm hlook.symm).symm
          | tail _ hrightTail =>
              exact ih htail left right hleftTail hrightTail hlhs hlook

theorem hasConflict_false_conflictFree
    [DecidableEq terminal] [DecidableEq nonterminal]
    (code : LL1ParserCode terminal nonterminal)
    (h : hasConflict code = false) :
    ConflictFree code :=
  hasConflictFrom_false_conflictFree code.entries h

theorem tableEntriesFor_mem {G : CFG terminal nonterminal}
    (entry : LL1ProductionEntry G)
    {lookahead : Option terminal}
    {lookaheads : List (Option terminal)}
    (hlook : lookahead ∈ lookaheads) :
    entry.toTableEntry lookahead ∈
      LL1ProductionEntry.tableEntriesFor entry lookaheads := by
  induction lookaheads with
  | nil =>
      cases hlook
  | cons head rest ih =>
      cases hlook with
      | head =>
          simp [LL1ProductionEntry.tableEntriesFor]
      | tail _ htail =>
          simp [LL1ProductionEntry.tableEntriesFor, ih htail]

theorem generateEntries_mem {G : CFG terminal nonterminal}
    (lookaheads : LL1ProductionEntry G -> List (Option terminal))
    {production : LL1ProductionEntry G}
    {productions : List (LL1ProductionEntry G)}
    {lookahead : Option terminal}
    (hprod : production ∈ productions)
    (hlook : lookahead ∈ lookaheads production) :
    production.toTableEntry lookahead ∈
      generateEntries lookaheads productions := by
  induction productions with
  | nil =>
      cases hprod
  | cons productionHead rest ih =>
      cases hprod with
      | head =>
          simp [generateEntries]
          exact Or.inl (tableEntriesFor_mem production hlook)
      | tail _ htail =>
          simp [generateEntries]
          exact Or.inr (ih htail)

theorem lookupFrom_complete_of_conflictFree
    [DecidableEq terminal] [DecidableEq nonterminal]
    {entries : List (LL1TableEntry terminal nonterminal)}
    (hfree :
      forall left right,
        left ∈ entries -> right ∈ entries ->
          left.lhs = right.lhs -> left.lookahead = right.lookahead ->
            left.rhs = right.rhs)
    {entry : LL1TableEntry terminal nonterminal}
    (hmem : entry ∈ entries) :
    lookupFrom entries entry.lhs entry.lookahead = some entry.rhs := by
  induction entries with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head =>
          simp [lookupFrom]
      | tail _ htail =>
          by_cases hlhs : head.lhs = entry.lhs
          · by_cases hlook : head.lookahead = entry.lookahead
            · have hrhs : head.rhs = entry.rhs :=
                hfree head entry (List.Mem.head rest)
                  (List.Mem.tail head htail) hlhs hlook
              simp [lookupFrom, hlhs, hlook, hrhs]
            · simp [lookupFrom, hlhs, hlook]
              apply ih
              · intro left right hleft hright
                exact hfree left right (by simp [hleft]) (by simp [hright])
              · exact htail
          · simp [lookupFrom, hlhs]
            apply ih
            · intro left right hleft hright
              exact hfree left right (by simp [hleft]) (by simp [hright])
            · exact htail

theorem generated_lookup_complete_of_conflictFree
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (lookaheads : LL1ProductionEntry G -> List (Option terminal))
    (hfree : ConflictFree (generated productions lookaheads))
    {production : LL1ProductionEntry G} {lookahead : Option terminal}
    (hprod : production ∈ productions)
    (hlook : lookahead ∈ lookaheads production) :
    (generated productions lookaheads).lookup production.lhs lookahead =
      some production.rhs := by
  change lookupFrom (generateEntries lookaheads productions)
      production.lhs lookahead = some production.rhs
  exact lookupFrom_complete_of_conflictFree
    (entries := generateEntries lookaheads productions)
    (entry := production.toTableEntry lookahead)
    hfree (generateEntries_mem lookaheads hprod hlook)

end LL1ParserCode

/-!
## Executable FIRST/FOLLOW Generation

The generator below fills the missing parser-generator side of the LL(1)
pipeline. It computes finite approximants for nullable nonterminals,
{lit}`FIRST` cells, and {lit}`FOLLOW` cells by iterating the usual data-flow
rules over a finite production list. The certified entry point checks that the
iteration has reached a fixed point and that the generated LL(1) table has no
conflicting cells before returning an executable parser.
-/

namespace LL1FirstFollow

structure State (terminal : Type u) (nonterminal : Type v) where
  nullable : List nonterminal
  first : List (nonterminal × terminal)
  follow : List (nonterminal × Option terminal)
deriving DecidableEq

def insertIfMissing [DecidableEq alpha] (x : alpha) (xs : List alpha) :
    List alpha :=
  if x ∈ xs then xs else x :: xs

def insertAll [DecidableEq beta] (f : alpha -> beta) :
    List alpha -> List beta -> List beta
  | [], acc => acc
  | x :: xs, acc => insertAll f xs (insertIfMissing (f x) acc)

namespace State

def nullableNT [DecidableEq nonterminal]
    (state : State terminal nonterminal) (A : nonterminal) : Bool :=
  decide (A ∈ state.nullable)

def firstForFrom [DecidableEq nonterminal] :
    List (nonterminal × terminal) -> nonterminal -> List terminal
  | [], _ => []
  | (B, a) :: rest, A =>
      if B = A then a :: firstForFrom rest A else firstForFrom rest A

def firstFor [DecidableEq nonterminal]
    (state : State terminal nonterminal) (A : nonterminal) : List terminal :=
  firstForFrom state.first A

def followForFrom [DecidableEq nonterminal] :
    List (nonterminal × Option terminal) -> nonterminal -> List (Option terminal)
  | [], _ => []
  | (B, lookahead) :: rest, A =>
      if B = A then lookahead :: followForFrom rest A else followForFrom rest A

def followFor [DecidableEq nonterminal]
    (state : State terminal nonterminal) (A : nonterminal) :
    List (Option terminal) :=
  followForFrom state.follow A

def addNullable [DecidableEq nonterminal]
    (state : State terminal nonterminal) (A : nonterminal) :
    State terminal nonterminal :=
  { state with nullable := insertIfMissing A state.nullable }

def addFirst [DecidableEq terminal] [DecidableEq nonterminal]
    (state : State terminal nonterminal) (A : nonterminal) (a : terminal) :
    State terminal nonterminal :=
  { state with first := insertIfMissing (A, a) state.first }

def addFollow [DecidableEq terminal] [DecidableEq nonterminal]
    (state : State terminal nonterminal) (A : nonterminal)
    (lookahead : Option terminal) : State terminal nonterminal :=
  { state with follow := insertIfMissing (A, lookahead) state.follow }

def addFirstList [DecidableEq terminal] [DecidableEq nonterminal]
    (A : nonterminal) : List terminal -> State terminal nonterminal ->
      State terminal nonterminal
  | [], state => state
  | a :: rest, state => addFirstList A rest (state.addFirst A a)

def addFollowList [DecidableEq terminal] [DecidableEq nonterminal]
    (A : nonterminal) : List (Option terminal) -> State terminal nonterminal ->
      State terminal nonterminal
  | [], state => state
  | lookahead :: rest, state =>
      addFollowList A rest (state.addFollow A lookahead)

end State

def nullableSymbol [DecidableEq nonterminal]
    (state : State terminal nonterminal) :
    Symbol terminal nonterminal -> Bool
  | Symbol.terminal _ => false
  | Symbol.nonterminal A => state.nullableNT A

def nullableSententialForm [DecidableEq nonterminal]
    (state : State terminal nonterminal) :
    SententialForm terminal nonterminal -> Bool
  | [] => true
  | symbol :: rest =>
      nullableSymbol state symbol && nullableSententialForm state rest

def firstSententialForm [DecidableEq nonterminal]
    (state : State terminal nonterminal) :
    SententialForm terminal nonterminal -> List terminal
  | [] => []
  | Symbol.terminal a :: _ => [a]
  | Symbol.nonterminal A :: rest =>
      state.firstFor A ++
        if state.nullableNT A then firstSententialForm state rest else []

def firstLookaheads [DecidableEq nonterminal]
    (state : State terminal nonterminal)
    (sent : SententialForm terminal nonterminal) : List (Option terminal) :=
  (firstSententialForm state sent).map some

def productionLookaheads [DecidableEq nonterminal]
    (state : State terminal nonterminal)
    (entry : LL1ProductionEntry (terminal := terminal) (nonterminal := nonterminal) G) :
    List (Option terminal) :=
  firstLookaheads state entry.rhs ++
    if nullableSententialForm state entry.rhs then
      state.followFor entry.lhs
    else
      []

def addFollowFromRhs [DecidableEq terminal] [DecidableEq nonterminal]
    (base : State terminal nonterminal) (lhs : nonterminal) :
    SententialForm terminal nonterminal -> State terminal nonterminal ->
      State terminal nonterminal
  | [], state => state
  | Symbol.terminal _ :: rest, state => addFollowFromRhs base lhs rest state
  | Symbol.nonterminal B :: rest, state =>
      let withFirst :=
        State.addFollowList B (firstLookaheads base rest) state
      let withNullable :=
        if nullableSententialForm base rest then
          State.addFollowList B (base.followFor lhs) withFirst
        else
          withFirst
      addFollowFromRhs base lhs rest withNullable

def stepProduction [DecidableEq terminal] [DecidableEq nonterminal]
    (entry : LL1ProductionEntry (terminal := terminal) (nonterminal := nonterminal) G)
    (state : State terminal nonterminal) :
    State terminal nonterminal :=
  let withNullable :=
    if nullableSententialForm state entry.rhs then
      state.addNullable entry.lhs
    else
      state
  let withFirst :=
    State.addFirstList entry.lhs (firstSententialForm state entry.rhs)
      withNullable
  addFollowFromRhs state entry.lhs entry.rhs withFirst

def step [DecidableEq terminal] [DecidableEq nonterminal]
    (productions :
      List (LL1ProductionEntry (terminal := terminal) (nonterminal := nonterminal) G))
    (state : State terminal nonterminal) :
    State terminal nonterminal :=
  productions.foldl (fun state entry => stepProduction entry state) state

def iterate (f : alpha -> alpha) : Nat -> alpha -> alpha
  | 0, x => x
  | n + 1, x => iterate f n (f x)

def initial (G : CFG terminal nonterminal) : State terminal nonterminal where
  nullable := []
  first := []
  follow := [(G.start, none)]

def compute [DecidableEq terminal] [DecidableEq nonterminal]
    (G : CFG terminal nonterminal)
    (productions : List (LL1ProductionEntry G)) (fuel : Nat) :
    State terminal nonterminal :=
  iterate (step productions) fuel (initial G)

def fixedPoint? [DecidableEq terminal] [DecidableEq nonterminal]
    (G : CFG terminal nonterminal)
    (productions : List (LL1ProductionEntry G)) (fuel : Nat) :
    Option (State terminal nonterminal) :=
  let state := compute G productions fuel
  if step productions state = state then some state else none

theorem fixedPoint?_stable [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {productions : List (LL1ProductionEntry G)} {fuel : Nat}
    {state : State terminal nonterminal}
    (h : fixedPoint? G productions fuel = some state) :
    step productions state = state := by
  unfold fixedPoint? at h
  by_cases hstable : step productions (compute G productions fuel) =
      compute G productions fuel
  · simp [hstable] at h
    cases h
    exact hstable
  · simp [hstable] at h

def generatedCode [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (state : State terminal nonterminal)
    (productions : List (LL1ProductionEntry G)) :
    LL1ParserCode terminal nonterminal :=
  LL1ParserCode.generated productions (productionLookaheads state)

def computedCode [DecidableEq terminal] [DecidableEq nonterminal]
    (G : CFG terminal nonterminal)
    (productions : List (LL1ProductionEntry G)) (fuel : Nat) :
    LL1ParserCode terminal nonterminal :=
  generatedCode (compute G productions fuel) productions

theorem computedCode_lookup_sound
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G)) (fuel : Nat) :
    forall A lookahead rhs,
      (computedCode G productions fuel).lookup A lookahead = some rhs ->
        G.produces A rhs := by
  exact LL1ParserCode.generated_lookup_sound productions
    (productionLookaheads (compute G productions fuel))

theorem computedCode_conflictFree_of_noConflict
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G)) (fuel : Nat)
    (h : LL1ParserCode.hasConflict
      (computedCode G productions fuel) = false) :
    LL1ParserCode.ConflictFree (computedCode G productions fuel) :=
  LL1ParserCode.hasConflict_false_conflictFree
    (computedCode G productions fuel) h

theorem computedCode_lookup_complete_of_noConflict
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G)) (fuel : Nat)
    (hfree : LL1ParserCode.hasConflict
      (computedCode G productions fuel) = false)
    {production : LL1ProductionEntry G} {lookahead : Option terminal}
    (hprod : production ∈ productions)
    (hlook : lookahead ∈
      productionLookaheads (compute G productions fuel) production) :
    (computedCode G productions fuel).lookup production.lhs lookahead =
      some production.rhs :=
  LL1ParserCode.generated_lookup_complete_of_conflictFree
    productions (productionLookaheads (compute G productions fuel))
    (computedCode_conflictFree_of_noConflict productions fuel hfree)
    hprod hlook

def certifiedParser? [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G)) (fuel : Nat) :
    Option (LL1Parser G) :=
  match fixedPoint? G productions fuel with
  | none => none
  | some state =>
      let code := generatedCode state productions
      if LL1ParserCode.hasConflict code then
        none
      else
        some (LL1ParserCode.generatedParser productions
          (productionLookaheads state))

def certifiedRun? [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (generatorFuel parserFuel : Nat) (w : Word terminal) :
    Option (CFG.ParseTree G (Symbol.nonterminal G.start)) :=
  match certifiedParser? productions generatorFuel with
  | none => none
  | some parser => LL1Parser.run parser parserFuel w

theorem certifiedRun?_sound
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    (productions : List (LL1ProductionEntry G))
    (generatorFuel parserFuel : Nat) (w : Word terminal)
    (tree : CFG.ParseTree G (Symbol.nonterminal G.start))
    (h : certifiedRun? productions generatorFuel parserFuel w = some tree) :
    w ∈ CFG.GeneratedLanguage G := by
  unfold certifiedRun? at h
  cases hparser : certifiedParser? productions generatorFuel with
  | none =>
      simp [hparser] at h
  | some parser =>
      simp [hparser] at h
      exact LL1Parser.run_sound parser parserFuel w tree h

end LL1FirstFollow

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

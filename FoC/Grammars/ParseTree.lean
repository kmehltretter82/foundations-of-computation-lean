import FoC.Grammars.CFG

namespace FoC
namespace Grammars

/-!
Parse trees for context-free grammars.

Used by:
- Chapter 4, Section 4.3: parsing, parse trees, and ambiguity.
-/

open Languages

namespace CFG

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

mutual

theorem ParseTree.derives {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    Derives G [s] (SententialForm.terminalWord (ParseTree.frontier tree)) := by
  cases tree with
  | leaf a =>
      exact Derives.refl _
  | node A rhs hprod children =>
      apply Derives.step
      · exact ⟨[], [], A, rhs, hprod, rfl, rfl⟩
      · simpa [ParseTree.frontier] using ParseForest.derives children

theorem ParseForest.derives {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    Derives G sent (SententialForm.terminalWord (ParseForest.frontier forest)) := by
  cases forest with
  | nil =>
      exact Derives.refl _
  | cons s restSent tree forest =>
      have hTree := ParseTree.derives tree
      have hForest := ParseForest.derives forest
      have hTreeContext :
          Derives G (s :: restSent)
            (SententialForm.terminalWord (ParseTree.frontier tree) ++ restSent) := by
        simpa using derives_context hTree [] restSent
      have hForestContext :
          Derives G
            (SententialForm.terminalWord (ParseTree.frontier tree) ++ restSent)
            (SententialForm.terminalWord (ParseTree.frontier tree) ++
              SententialForm.terminalWord (ParseForest.frontier forest)) := by
        simpa [List.append_assoc] using derives_context hForest
          (SententialForm.terminalWord (ParseTree.frontier tree)) []
      have hAll := derives_trans hTreeContext hForestContext
      change Derives G (s :: restSent)
        (SententialForm.terminalWord
          (Word.Concat (ParseTree.frontier tree) (ParseForest.frontier forest)))
      rw [SententialForm.terminalWord_append]
      exact hAll

end

def ParseTreeGenerates (G : CFG terminal nonterminal) (w : Word terminal) : Prop :=
  exists tree : ParseTree G (Symbol.nonterminal G.start),
    ParseTree.frontier tree = w

theorem parseTree_generates_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : ParseTreeGenerates G w) :
    w ∈ GeneratedLanguage G := by
  cases h with
  | intro tree hfrontier =>
      have hDerives := ParseTree.derives tree
      rw [hfrontier] at hDerives
      exact hDerives

def AmbiguousByParseTrees (G : CFG terminal nonterminal) : Prop :=
  exists w, exists t1 : ParseTree G (Symbol.nonterminal G.start),
    exists t2 : ParseTree G (Symbol.nonterminal G.start),
      ParseTree.frontier t1 = w ∧
      ParseTree.frontier t2 = w ∧
      t1 ≠ t2

end CFG

end Grammars
end FoC

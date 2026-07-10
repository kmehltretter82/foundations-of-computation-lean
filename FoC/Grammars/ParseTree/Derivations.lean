import FoC.Grammars.ParseTree.Basic

set_option doc.verso true

namespace FoC
namespace Grammars

open Languages

namespace CFG

/-!
# Parse Trees and Derivations

This module translates trees and forests to CFG derivations, reconstructs forests from terminal derivations, and provides the selected-subtree hole and frontier decomposition lemmas used later.
-/

/-!
## Derivations from trees

Every parse tree gives a grammar derivation of its frontier, and the selected
subtree lemmas expose a context around a nested nonterminal subtree.
-/

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

mutual

/-
Selected-subtree derivations decompose a tree into a context and one chosen
nonterminal subtree. The hole form records the context; a derivation of the
selected subtree can then be plugged back into that context.
-/

theorem ParseTree.derives_with_selected_subtree_hole
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    exists u v : Word terminal,
      ParseTree.frontier tree =
        Word.Concat u (Word.Concat (NonterminalSubtree.frontier subtree) v) ∧
      Derives G [s]
        (SententialForm.terminalWord u ++
          [Symbol.nonterminal (NonterminalSubtree.root subtree)] ++
          SententialForm.terminalWord v) := by
  cases tree with
  | leaf a =>
      cases hget
  | node A rhs hprod children =>
      cases i with
      | zero =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases hget
          exists []
          exists []
          constructor
          · simp [ParseTree.frontier, NonterminalSubtree.frontier, Word.Concat]
          · exact Derives.refl _
      | succ i =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases ParseForest.derives_with_selected_subtree_hole children hget with
          | intro u hu =>
              cases hu with
              | intro v hv =>
                  exists u
                  exists v
                  constructor
                  · exact hv.left
                  · have hstep : Yields G [Symbol.nonterminal A] rhs := by
                      exists []
                      exists []
                      exists A
                      exists rhs
                      constructor
                      · exact hprod
                      constructor
                      · rfl
                      · simp
                    exact Derives.step hstep hv.right

theorem ParseForest.derives_with_selected_subtree_hole
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseForest.longestNonterminalSubtrees forest)[i]? = some subtree) :
    exists u v : Word terminal,
      ParseForest.frontier forest =
        Word.Concat u (Word.Concat (NonterminalSubtree.frontier subtree) v) ∧
      Derives G sent
        (SententialForm.terminalWord u ++
          [Symbol.nonterminal (NonterminalSubtree.root subtree)] ++
          SententialForm.terminalWord v) := by
  cases forest with
  | nil =>
      cases hget
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        cases ParseForest.derives_with_selected_subtree_hole rest hget with
        | intro u hu =>
            cases hu with
            | intro v hv =>
                exists Word.Concat (ParseTree.frontier tree) u
                exists v
                constructor
                · simp [ParseForest.frontier, hv.left, Word.Concat, List.append_assoc]
                · have hTree := ParseTree.derives tree
                  have hTreeContext :
                      Derives G (s :: restSent)
                        (SententialForm.terminalWord (ParseTree.frontier tree) ++
                          restSent) := by
                    simpa using derives_context hTree [] restSent
                  have hRestContext :
                      Derives G
                        (SententialForm.terminalWord (ParseTree.frontier tree) ++
                          restSent)
                        (SententialForm.terminalWord (ParseTree.frontier tree) ++
                          (SententialForm.terminalWord u ++
                            [Symbol.nonterminal
                              (NonterminalSubtree.root subtree)] ++
                            SententialForm.terminalWord v)) := by
                    simpa [List.append_assoc] using
                      derives_context hv.right
                        (SententialForm.terminalWord
                          (ParseTree.frontier tree)) []
                  have hAll := derives_trans hTreeContext hRestContext
                  have htarget :
                      SententialForm.terminalWord
                          (Word.Concat (ParseTree.frontier tree) u) ++
                        [Symbol.nonterminal
                          (NonterminalSubtree.root subtree)] ++
                        SententialForm.terminalWord v =
                      SententialForm.terminalWord (ParseTree.frontier tree) ++
                        (SententialForm.terminalWord u ++
                          [Symbol.nonterminal
                            (NonterminalSubtree.root subtree)] ++
                          SententialForm.terminalWord v) := by
                    simp [SententialForm.terminalWord, Word.Concat,
                      List.append_assoc]
                  rw [htarget]
                  exact hAll
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        cases ParseTree.derives_with_selected_subtree_hole tree hget with
        | intro u hu =>
            cases hu with
            | intro v hv =>
                exists u
                exists Word.Concat v (ParseForest.frontier rest)
                constructor
                · simp [ParseForest.frontier, hv.left, Word.Concat, List.append_assoc]
                · let hole :=
                    SententialForm.terminalWord u ++
                      [Symbol.nonterminal
                        (NonterminalSubtree.root subtree)] ++
                      SententialForm.terminalWord v
                  have hTreeContext :
                      Derives G (s :: restSent) (hole ++ restSent) := by
                    simpa [hole] using derives_context hv.right [] restSent
                  have hRest := ParseForest.derives rest
                  have hRestContext :
                      Derives G (hole ++ restSent)
                        (hole ++
                          SententialForm.terminalWord
                            (ParseForest.frontier rest)) := by
                    simpa [hole] using derives_context hRest hole []
                  have hAll := derives_trans hTreeContext hRestContext
                  have htarget :
                      hole ++
                        SententialForm.terminalWord (ParseForest.frontier rest) =
                      SententialForm.terminalWord u ++
                        [Symbol.nonterminal
                          (NonterminalSubtree.root subtree)] ++
                        SententialForm.terminalWord
                          (Word.Concat v (ParseForest.frontier rest)) := by
                    simp [hole, SententialForm.terminalWord, Word.Concat,
                      List.append_assoc]
                  rw [← htarget]
                  exact hAll

end

mutual

/-
The frontier lemmas below are bookkeeping for forests. They make the append
structure of a forest visible at the word level, which is necessary when a
derivation step splits a sentential form into left context, subtree, and right
context.
-/

theorem ParseTree.frontier_append_dummy {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (_tree : ParseTree G s) : True := by
  trivial

theorem ParseForest.frontier_append {G : CFG terminal nonterminal}
    {left right : SententialForm terminal nonterminal}
    (leftForest : ParseForest G left) (rightForest : ParseForest G right) :
    ParseForest.frontier (ParseForest.append leftForest rightForest) =
      Word.Concat (ParseForest.frontier leftForest)
        (ParseForest.frontier rightForest) := by
  cases leftForest with
  | nil =>
      rfl
  | cons s rest tree forest =>
      have ih := ParseForest.frontier_append forest rightForest
      simp [ParseForest.append, ParseForest.frontier, ih, Word.Concat,
        List.append_assoc]

end

theorem ParseForest.frontier_terminalWord {G : CFG terminal nonterminal}
    (w : Word terminal) :
    ParseForest.frontier
        (ParseForest.terminalWord (G := G) (nonterminal := nonterminal) w) = w := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      simp [ParseForest.terminalWord, ParseForest.frontier, ParseTree.frontier,
        Word.Concat, ih]

theorem ParseForest.exists_split_append {G : CFG terminal nonterminal}
    {left right : SententialForm terminal nonterminal}
    (forest : ParseForest G (left ++ right)) :
    exists leftForest : ParseForest G left,
      exists rightForest : ParseForest G right,
        ParseForest.frontier forest =
          Word.Concat (ParseForest.frontier leftForest)
            (ParseForest.frontier rightForest) := by
  induction left with
  | nil =>
      exact ⟨ParseForest.nil, forest, rfl⟩
  | cons s rest ih =>
      cases forest with
      | cons _ _ tree forestTail =>
          cases ih forestTail with
          | intro leftTail hleftTail =>
              cases hleftTail with
              | intro rightForest hrightForest =>
                  exists ParseForest.cons s rest tree leftTail
                  exists rightForest
                  simp [ParseForest.frontier, hrightForest, Word.Concat,
                    List.append_assoc]

/-!
The next direction reconstructs parse forests from derivations. One yield step
is inverted by splitting the existing forest around the rewritten substring and
replacing the production's right-hand-side forest with a single node.
-/

theorem ParseForest.of_yields_of_forest {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (hstep : Yields G x y) (forestY : ParseForest G y) :
    exists forestX : ParseForest G x,
      ParseForest.frontier forestX = ParseForest.frontier forestY := by
  cases hstep with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          subst x
                          subst y
                          cases ParseForest.exists_split_append
                              (left := u ++ rhs) (right := v) forestY with
                          | intro forestLeft hforestLeft =>
                              cases hforestLeft with
                              | intro forestV houterSplit =>
                                  cases ParseForest.exists_split_append
                                      (left := u) (right := rhs) forestLeft with
                                  | intro forestU hforestU =>
                                      cases hforestU with
                                      | intro forestRhs hinnerSplit =>
                                          let treeA :=
                                            ParseTree.node A rhs hprod forestRhs
                                          let forestA :=
                                            ParseForest.cons
                                              (Symbol.nonterminal A) []
                                              treeA ParseForest.nil
                                          let forestX :=
                                            ParseForest.append
                                              (ParseForest.append forestU forestA)
                                              forestV
                                          exists forestX
                                          rw [houterSplit, hinnerSplit]
                                          simp [forestX, treeA,
                                            forestA,
                                            ParseForest.frontier_append,
                                            ParseForest.frontier,
                                            ParseTree.frontier, Word.Concat,
                                            List.append_assoc]

theorem ParseForest.of_derives_toWord {G : CFG terminal nonterminal}
    {sf out : SententialForm terminal nonterminal} {w : Word terminal}
    (h : Derives G sf out) (hout : SententialForm.toWord? out = some w) :
    exists forest : ParseForest G sf, ParseForest.frontier forest = w := by
  induction h with
  | refl x =>
      have hx : x = SententialForm.terminalWord w :=
        SententialForm.toWord?_some_eq_terminalWord hout
      subst x
      exact ⟨ParseForest.terminalWord w, ParseForest.frontier_terminalWord w⟩
  | step hstep hder ih =>
      cases ih hout with
      | intro forestY hforestY =>
          cases ParseForest.of_yields_of_forest hstep forestY with
          | intro forestX hforestX =>
              exists forestX
              rw [hforestX, hforestY]

theorem ParseForest.of_derives_terminal {G : CFG terminal nonterminal}
    {sf : SententialForm terminal nonterminal} {w : Word terminal}
    (h : Derives G sf (SententialForm.terminalWord w)) :
    exists forest : ParseForest G sf, ParseForest.frontier forest = w :=
  ParseForest.of_derives_toWord h (SententialForm.terminalWord_toWord w)

theorem ParseTree.of_generates_language {G : CFG terminal nonterminal}
    {w : Word terminal} (h : w ∈ GeneratedLanguage G) :
    exists tree : ParseTree G (Symbol.nonterminal G.start),
      ParseTree.frontier tree = w := by
  cases ParseForest.of_derives_terminal h with
  | intro forest hforest =>
      cases forest with
      | cons _ _ tree rest =>
          cases rest with
          | nil =>
              exists tree
              simpa [ParseForest.frontier, Word.Concat] using hforest

end CFG
end Grammars
end FoC

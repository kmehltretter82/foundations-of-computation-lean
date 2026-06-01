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

def NonterminalSubtree (G : CFG terminal nonterminal) : Type _ :=
  Sigma (fun A : nonterminal => ParseTree G (Symbol.nonterminal A))

namespace NonterminalSubtree

def root {G : CFG terminal nonterminal} (subtree : NonterminalSubtree G) :
    nonterminal :=
  subtree.1

end NonterminalSubtree

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

end NonterminalSubtree

def ParseTree.MinimalForFrontier {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) : Prop :=
  forall other : ParseTree G s,
    ParseTree.frontier other = ParseTree.frontier tree ->
      ParseTree.nodeCount tree <= ParseTree.nodeCount other

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

mutual

theorem ParseTree.longestNonterminalPath_length
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    (ParseTree.longestNonterminalPath tree).length = ParseTree.height tree := by
  cases tree with
  | leaf a =>
      simp [ParseTree.longestNonterminalPath, ParseTree.height]
  | node A rhs hprod children =>
      have hChildren := ParseForest.longestNonterminalPath_length children
      simp [ParseTree.longestNonterminalPath, ParseTree.height, hChildren]

theorem ParseForest.longestNonterminalPath_length
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    (ParseForest.longestNonterminalPath forest).length = ParseForest.height forest := by
  cases forest with
  | nil =>
      simp [ParseForest.longestNonterminalPath, ParseForest.height]
  | cons s restSent tree rest =>
      have hTree := ParseTree.longestNonterminalPath_length tree
      have hRest := ParseForest.longestNonterminalPath_length rest
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalPath, ParseForest.height, hlt, hRest]
        exact (Nat.max_eq_right (Nat.le_of_lt hlt)).symm
      · simp [ParseForest.longestNonterminalPath, ParseForest.height, hlt, hTree]
        have hle : ParseForest.height rest <= ParseTree.height tree := by omega
        exact (Nat.max_eq_left hle).symm

end

mutual

theorem ParseTree.longestNonterminalSubtrees_length
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    (ParseTree.longestNonterminalSubtrees tree).length = ParseTree.height tree := by
  cases tree with
  | leaf a =>
      simp [ParseTree.longestNonterminalSubtrees, ParseTree.height]
  | node A rhs hprod children =>
      have hChildren := ParseForest.longestNonterminalSubtrees_length children
      simp [ParseTree.longestNonterminalSubtrees, ParseTree.height, hChildren]

theorem ParseForest.longestNonterminalSubtrees_length
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    (ParseForest.longestNonterminalSubtrees forest).length = ParseForest.height forest := by
  cases forest with
  | nil =>
      simp [ParseForest.longestNonterminalSubtrees, ParseForest.height]
  | cons s restSent tree rest =>
      have hTree := ParseTree.longestNonterminalSubtrees_length tree
      have hRest := ParseForest.longestNonterminalSubtrees_length rest
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, ParseForest.height, hlt, hRest]
        exact (Nat.max_eq_right (Nat.le_of_lt hlt)).symm
      · simp [ParseForest.longestNonterminalSubtrees, ParseForest.height, hlt, hTree]
        have hle : ParseForest.height rest <= ParseTree.height tree := by omega
        exact (Nat.max_eq_left hle).symm

end

mutual

theorem ParseTree.longestNonterminalSubtrees_roots
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    (ParseTree.longestNonterminalSubtrees tree).map
        (fun subtree => NonterminalSubtree.root subtree) =
      ParseTree.longestNonterminalPath tree := by
  cases tree with
  | leaf a =>
      simp [ParseTree.longestNonterminalSubtrees, ParseTree.longestNonterminalPath]
  | node A rhs hprod children =>
      have hChildren := ParseForest.longestNonterminalSubtrees_roots children
      simp [ParseTree.longestNonterminalSubtrees, ParseTree.longestNonterminalPath,
        NonterminalSubtree.root]
      simpa [NonterminalSubtree.root] using hChildren

theorem ParseForest.longestNonterminalSubtrees_roots
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    (ParseForest.longestNonterminalSubtrees forest).map
        (fun subtree => NonterminalSubtree.root subtree) =
      ParseForest.longestNonterminalPath forest := by
  cases forest with
  | nil =>
      simp [ParseForest.longestNonterminalSubtrees, ParseForest.longestNonterminalPath]
  | cons s restSent tree rest =>
      have hTree := ParseTree.longestNonterminalSubtrees_roots tree
      have hRest := ParseForest.longestNonterminalSubtrees_roots rest
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, ParseForest.longestNonterminalPath,
          hlt, hRest]
      · simp [ParseForest.longestNonterminalSubtrees, ParseForest.longestNonterminalPath,
          hlt, hTree]

end

mutual

theorem ParseTree.longestNonterminalPath_all_mem
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {A : nonterminal}
    (hA : A ∈ ParseTree.longestNonterminalPath tree) :
    A ∈ G.nonterminalsFinite.elems := by
  cases tree with
  | leaf a =>
      cases hA
  | node B rhs hprod children =>
      simp [ParseTree.longestNonterminalPath] at hA
      cases hA with
      | inl hEq =>
          rw [hEq]
          exact G.nonterminalsFinite.complete B
      | inr hTail =>
          exact ParseForest.longestNonterminalPath_all_mem children hTail

theorem ParseForest.longestNonterminalPath_all_mem
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {A : nonterminal}
    (hA : A ∈ ParseForest.longestNonterminalPath forest) :
    A ∈ G.nonterminalsFinite.elems := by
  cases forest with
  | nil =>
      cases hA
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalPath, hlt] at hA
        exact ParseForest.longestNonterminalPath_all_mem rest hA
      · simp [ParseForest.longestNonterminalPath, hlt] at hA
        exact ParseTree.longestNonterminalPath_all_mem tree hA

end

theorem ParseTree.exists_duplicate_nonterminal_on_long_path
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < ParseTree.height tree) :
    exists i j A,
      i < j ∧
      j < ParseTree.height tree ∧
      (ParseTree.longestNonterminalPath tree)[i]? = some A ∧
      (ParseTree.longestNonterminalPath tree)[j]? = some A := by
  let path := ParseTree.longestNonterminalPath tree
  have hlen : G.nonterminalsFinite.elems.length < path.length := by
    simpa [path, ParseTree.longestNonterminalPath_length tree] using hheight
  have hall : forall A, A ∈ path -> A ∈ G.nonterminalsFinite.elems := by
    intro A hA
    exact ParseTree.longestNonterminalPath_all_mem tree hA
  cases Foundation.list_duplicate_indices_of_length_gt hlen hall with
  | intro i hi =>
      cases hi with
      | intro j hj =>
          cases hj with
          | intro A hA =>
              exists i
              exists j
              exists A
              constructor
              · exact hA.left
              constructor
              · have hjPath : j < path.length := hA.right.left
                simpa [path, ParseTree.longestNonterminalPath_length tree] using hjPath
              · exact hA.right.right

theorem ParseTree.exists_duplicate_root_subtrees_on_long_path
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < ParseTree.height tree) :
    exists i j upper lower,
      i < j ∧
      j < ParseTree.height tree ∧
      (ParseTree.longestNonterminalSubtrees tree)[i]? = some upper ∧
      (ParseTree.longestNonterminalSubtrees tree)[j]? = some lower ∧
      NonterminalSubtree.root upper = NonterminalSubtree.root lower := by
  cases ParseTree.exists_duplicate_nonterminal_on_long_path tree hheight with
  | intro i hi =>
      cases hi with
      | intro j hj =>
          cases hj with
          | intro A hA =>
              have hRootI :
                  ((ParseTree.longestNonterminalSubtrees tree).map
                    (fun subtree => NonterminalSubtree.root subtree))[i]? = some A := by
                rw [ParseTree.longestNonterminalSubtrees_roots tree]
                exact hA.right.right.left
              have hRootJ :
                  ((ParseTree.longestNonterminalSubtrees tree).map
                    (fun subtree => NonterminalSubtree.root subtree))[j]? = some A := by
                rw [ParseTree.longestNonterminalSubtrees_roots tree]
                exact hA.right.right.right
              cases Foundation.list_getElem?_of_map_eq_some hRootI with
              | intro upper hUpper =>
                  cases Foundation.list_getElem?_of_map_eq_some hRootJ with
                  | intro lower hLower =>
                      exists i
                      exists j
                      exists upper
                      exists lower
                      constructor
                      · exact hA.left
                      constructor
                      · exact hA.right.left
                      constructor
                      · exact hUpper.left
                      constructor
                      · exact hLower.left
                      · exact Eq.trans hUpper.right hLower.right.symm

mutual

theorem ParseTree.longestNonterminalSubtree_frontier_context
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {subtree : NonterminalSubtree G}
    (hsub : subtree ∈ ParseTree.longestNonterminalSubtrees tree) :
    exists u v : Word terminal,
      ParseTree.frontier tree =
        Word.Concat u (Word.Concat (NonterminalSubtree.frontier subtree) v) := by
  cases tree with
  | leaf a =>
      cases hsub
  | node A rhs hprod children =>
      simp [ParseTree.longestNonterminalSubtrees] at hsub
      cases hsub with
      | inl hhead =>
          subst subtree
          exists []
          exists []
          simp [ParseTree.frontier, NonterminalSubtree.frontier, Word.Concat]
      | inr htail =>
          exact ParseForest.longestNonterminalSubtree_frontier_context children htail

theorem ParseForest.longestNonterminalSubtree_frontier_context
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {subtree : NonterminalSubtree G}
    (hsub : subtree ∈ ParseForest.longestNonterminalSubtrees forest) :
    exists u v : Word terminal,
      ParseForest.frontier forest =
        Word.Concat u (Word.Concat (NonterminalSubtree.frontier subtree) v) := by
  cases forest with
  | nil =>
      cases hsub
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hsub
        cases ParseForest.longestNonterminalSubtree_frontier_context rest hsub with
        | intro u hu =>
            cases hu with
            | intro v hv =>
                exists Word.Concat (ParseTree.frontier tree) u
                exists v
                simp [ParseForest.frontier, Word.Concat, hv, List.append_assoc]
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hsub
        cases ParseTree.longestNonterminalSubtree_frontier_context tree hsub with
        | intro u hu =>
            cases hu with
            | intro v hv =>
                exists u
                exists Word.Concat v (ParseForest.frontier rest)
                simp [ParseForest.frontier, Word.Concat, hv, List.append_assoc]

end

theorem ParseTree.longestNonterminalSubtree_get_frontier_context
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    exists u v : Word terminal,
      ParseTree.frontier tree =
        Word.Concat u (Word.Concat (NonterminalSubtree.frontier subtree) v) :=
  ParseTree.longestNonterminalSubtree_frontier_context tree
    (List.mem_of_getElem? hget)

theorem ParseTree.exists_minimal_for_frontier
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    exists minTree : ParseTree G s,
      ParseTree.frontier minTree = ParseTree.frontier tree ∧
      ParseTree.MinimalForFrontier minTree := by
  classical
  let P : Nat -> Prop := fun n =>
    forall {s : Symbol terminal nonterminal} (tree : ParseTree G s),
      ParseTree.nodeCount tree = n ->
        exists minTree : ParseTree G s,
          ParseTree.frontier minTree = ParseTree.frontier tree ∧
          ParseTree.MinimalForFrontier minTree
  have hmain : forall n, P n := by
    intro n
    exact Nat.strongRecOn n (motive := P) (fun n ih => by
        intro s tree hcount
        by_cases hmin : ParseTree.MinimalForFrontier tree
        · exact ⟨tree, rfl, hmin⟩
        · have hsmaller :
              exists other : ParseTree G s,
                ParseTree.frontier other = ParseTree.frontier tree ∧
                ParseTree.nodeCount other < ParseTree.nodeCount tree := by
            apply Classical.byContradiction
            intro hnone
            apply hmin
            intro other hfrontier
            by_cases hlt : ParseTree.nodeCount other < ParseTree.nodeCount tree
            · exact False.elim (hnone ⟨other, hfrontier, hlt⟩)
            · exact Nat.le_of_not_gt hlt
          cases hsmaller with
          | intro other hother =>
              have hotherCount :
                  ParseTree.nodeCount other < n := by
                rw [← hcount]
                exact hother.right
              cases ih (ParseTree.nodeCount other) hotherCount other rfl with
              | intro minTree hminTree =>
                  exists minTree
                  constructor
                  · exact Eq.trans hminTree.left hother.left
                  · exact hminTree.right)
  exact hmain (ParseTree.nodeCount tree) tree rfl

mutual

theorem ParseTree.frontier_length_le_pow
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    Word.Length (ParseTree.frontier tree) <= B ^ ParseTree.height tree := by
  cases tree with
  | leaf a =>
      simp [ParseTree.frontier, ParseTree.height, Word.Length]
  | node A rhs hprod children =>
      have hForest := ParseForest.frontier_length_le_pow hB hBound children
      have hRhs := hBound A rhs hprod
      simp [ParseTree.frontier, ParseTree.height]
      calc
        Word.Length (ParseForest.frontier children) <=
            rhs.length * B ^ ParseForest.height children := hForest
        _ <= B * B ^ ParseForest.height children := by
          exact Nat.mul_le_mul_right _ (Nat.le_of_lt hRhs)
        _ = B ^ (ParseForest.height children + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]

theorem ParseForest.frontier_length_le_pow
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    Word.Length (ParseForest.frontier forest) <=
      sent.length * B ^ ParseForest.height forest := by
  cases forest with
  | nil =>
      simp [ParseForest.frontier, ParseForest.height, Word.Length]
  | cons s restSent tree rest =>
      have hTree := ParseTree.frontier_length_le_pow hB hBound tree
      have hRest := ParseForest.frontier_length_le_pow hB hBound rest
      have hTreePow :
          B ^ ParseTree.height tree <=
            B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) :=
        Nat.pow_le_pow_right hB (Nat.le_max_left _ _)
      have hRestPow :
          B ^ ParseForest.height rest <=
            B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) :=
        Nat.pow_le_pow_right hB (Nat.le_max_right _ _)
      have hTreeBound :
          Word.Length (ParseTree.frontier tree) <=
            B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) :=
        Nat.le_trans hTree hTreePow
      have hRestBound :
          Word.Length (ParseForest.frontier rest) <=
            restSent.length *
              B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) :=
        Nat.le_trans hRest (Nat.mul_le_mul_left restSent.length hRestPow)
      rw [ParseForest.frontier, Word.length_concat]
      simp [ParseForest.height]
      have hsum := Nat.add_le_add hTreeBound hRestBound
      calc
        Word.Length (ParseTree.frontier tree) +
            Word.Length (ParseForest.frontier rest) <=
            B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) +
              restSent.length *
                B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) :=
          hsum
        _ = (restSent.length + 1) *
              B ^ Nat.max (ParseTree.height tree) (ParseForest.height rest) := by
          symm
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

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

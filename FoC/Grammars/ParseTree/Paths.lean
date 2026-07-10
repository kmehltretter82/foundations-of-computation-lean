import FoC.Grammars.ParseTree.Derivations

set_option doc.verso true

namespace FoC
namespace Grammars

open Languages

namespace CFG

/-!
# Parse-Tree Paths and Selected Subtrees

Longest nonterminal paths expose repeated roots in sufficiently tall trees. This module proves the path-length, suffix, membership, duplicate-root, frontier-context, and minimal-tree existence lemmas.
-/

/-!
The height and selected-subtree lemmas prepare the pumping-style arguments. A
longest nonterminal path is mirrored by a list of actual subtrees, so repeated
nonterminal names can later be turned into a nested pair of parse subtrees.
-/

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
        have hle : ParseForest.height rest <= ParseTree.height tree := by lia
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
        have hle : ParseForest.height rest <= ParseTree.height tree := by lia
        exact (Nat.max_eq_left hle).symm

end

mutual

theorem ParseTree.longestNonterminalSubtree_height_at_index
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    NonterminalSubtree.height subtree + i = ParseTree.height tree := by
  cases tree with
  | leaf a =>
      cases hget
  | node A rhs hprod children =>
      cases i with
      | zero =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases hget
          simp [NonterminalSubtree.height, ParseTree.height]
      | succ i =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          have hChild :=
            ParseForest.longestNonterminalSubtree_height_at_index children hget
          simp [ParseTree.height]
          lia

theorem ParseForest.longestNonterminalSubtree_height_at_index
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseForest.longestNonterminalSubtrees forest)[i]? = some subtree) :
    NonterminalSubtree.height subtree + i = ParseForest.height forest := by
  cases forest with
  | nil =>
      cases hget
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        have hRest :=
          ParseForest.longestNonterminalSubtree_height_at_index rest hget
        have hmax :
            Nat.max (ParseTree.height tree) (ParseForest.height rest) =
              ParseForest.height rest :=
          Nat.max_eq_right (Nat.le_of_lt hlt)
        simp [ParseForest.height, hmax]
        exact hRest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        have hTree :=
          ParseTree.longestNonterminalSubtree_height_at_index tree hget
        have hle : ParseForest.height rest <= ParseTree.height tree := by
          lia
        have hmax :
            Nat.max (ParseTree.height tree) (ParseForest.height rest) =
              ParseTree.height tree :=
          Nat.max_eq_left hle
        simp [ParseForest.height, hmax]
        exact hTree

end

mutual

theorem ParseTree.longestNonterminalSubtrees_suffix_at_index
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    List.drop i (ParseTree.longestNonterminalSubtrees tree) =
      ParseTree.longestNonterminalSubtrees subtree.2 := by
  cases tree with
  | leaf a =>
      cases hget
  | node A rhs hprod children =>
      cases i with
      | zero =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases hget
          simp [ParseTree.longestNonterminalSubtrees]
      | succ i =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          have hChild :=
            ParseForest.longestNonterminalSubtrees_suffix_at_index children hget
          simp [ParseTree.longestNonterminalSubtrees, hChild]

theorem ParseForest.longestNonterminalSubtrees_suffix_at_index
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseForest.longestNonterminalSubtrees forest)[i]? = some subtree) :
    List.drop i (ParseForest.longestNonterminalSubtrees forest) =
      ParseTree.longestNonterminalSubtrees subtree.2 := by
  cases forest with
  | nil =>
      cases hget
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        have hRest :=
          ParseForest.longestNonterminalSubtrees_suffix_at_index rest hget
        simp [ParseForest.longestNonterminalSubtrees, hlt, hRest]
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        have hTree :=
          ParseTree.longestNonterminalSubtrees_suffix_at_index tree hget
        simp [ParseForest.longestNonterminalSubtrees, hlt, hTree]

end

/-!
The next group connects the selected-subtree list back to finite nonterminal
sets. Long paths force duplicate roots by pigeonhole, and the "near bottom"
version chooses a duplicate whose upper subtree has bounded height.
-/

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

/-
A longest path with more nonterminal nodes than the finite nonterminal set must
repeat a root label. The following lemmas refine that pigeonhole fact into
actual subtrees on the path.

The finite bound is measured by the grammar's witness list. Because
{lit}`FiniteType` permits duplicates, the length is a valid upper bound for
this argument rather than a canonical nonterminal count.
-/

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

/-
For pumping, it is not enough to find any duplicate labels; the repeated
subtrees must be positioned near the bottom so their frontiers are bounded. This
lemma selects that lower pair.
-/

theorem ParseTree.exists_duplicate_root_subtrees_near_bottom
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < ParseTree.height tree) :
    exists i j upper lower,
      i < j ∧
      j < ParseTree.height tree ∧
      (ParseTree.longestNonterminalSubtrees tree)[i]? = some upper ∧
      (ParseTree.longestNonterminalSubtrees tree)[j]? = some lower ∧
      NonterminalSubtree.root upper = NonterminalSubtree.root lower ∧
      NonterminalSubtree.height upper <=
        G.nonterminalsFinite.elems.length + 1 := by
  let subtrees := ParseTree.longestNonterminalSubtrees tree
  let roots := subtrees.map (fun subtree => NonterminalSubtree.root subtree)
  let offset := ParseTree.height tree - (G.nonterminalsFinite.elems.length + 1)
  let suffix := List.drop offset roots
  have hrootsLen : roots.length = ParseTree.height tree := by
    simp [roots, subtrees, ParseTree.longestNonterminalSubtrees_length tree]
  have hsuffixLen : suffix.length = G.nonterminalsFinite.elems.length + 1 := by
    rw [show suffix.length = roots.length - offset by simp [suffix]]
    rw [hrootsLen]
    simp [offset]
    lia
  have hsuffixLong :
      G.nonterminalsFinite.elems.length < suffix.length := by
    rw [hsuffixLen]
    lia
  have hall : forall A, A ∈ suffix -> A ∈ G.nonterminalsFinite.elems := by
    intro A hA
    have hRootMem : A ∈ roots := List.mem_of_mem_drop hA
    have hPathMem : A ∈ ParseTree.longestNonterminalPath tree := by
      simpa [roots, subtrees, ParseTree.longestNonterminalSubtrees_roots tree]
        using hRootMem
    exact ParseTree.longestNonterminalPath_all_mem tree hPathMem
  cases Foundation.list_duplicate_indices_of_length_gt hsuffixLong hall with
  | intro p hp =>
      cases hp with
      | intro q hq =>
          cases hq with
          | intro A hA =>
              have hRootP : roots[offset + p]? = some A := by
                have hdrop := hA.right.right.left
                have hdrop' :
                    (List.drop offset roots)[p]? = some A := by
                  simpa [suffix] using hdrop
                rw [List.getElem?_drop] at hdrop'
                exact hdrop'
              have hRootQ : roots[offset + q]? = some A := by
                have hdrop := hA.right.right.right
                have hdrop' :
                    (List.drop offset roots)[q]? = some A := by
                  simpa [suffix] using hdrop
                rw [List.getElem?_drop] at hdrop'
                exact hdrop'
              cases Foundation.list_getElem?_of_map_eq_some hRootP with
              | intro upper hUpper =>
                  cases Foundation.list_getElem?_of_map_eq_some hRootQ with
                  | intro lower hLower =>
                      exists offset + p
                      exists offset + q
                      exists upper
                      exists lower
                      constructor
                      · lia
                      constructor
                      · have hqLen : q < suffix.length := hA.right.left
                        rw [hsuffixLen] at hqLen
                        simp [offset]
                        lia
                      constructor
                      · exact hUpper.left
                      constructor
                      · exact hLower.left
                      constructor
                      · exact Eq.trans hUpper.right hLower.right.symm
                      · have hUpperHeight :=
                          ParseTree.longestNonterminalSubtree_height_at_index
                            tree hUpper.left
                        simp [offset] at hUpperHeight
                        lia

mutual

/-
The frontier-context lemmas recover the terminal words around a selected
nonterminal subtree. They connect the structural longest-path choice to the word
decomposition needed by language statements.
-/

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

end CFG
end Grammars
end FoC

import FoC.Grammars.ParseTreePart1

set_option doc.verso true

namespace FoC
namespace Grammars
namespace CFG
open Languages

theorem ParseTree.loop_derivation_from_repeated_selected_subtrees_nonempty
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hminimal : ParseTree.MinimalForFrontier tree)
    {i j : Nat} {upper lower : NonterminalSubtree G}
    (hij : i < j)
    (hupper : (ParseTree.longestNonterminalSubtrees tree)[i]? = some upper)
    (hlower : (ParseTree.longestNonterminalSubtrees tree)[j]? = some lower)
    (hroot : NonterminalSubtree.root upper = NonterminalSubtree.root lower) :
    exists x z : Word terminal,
      NonterminalSubtree.frontier upper =
        Word.Concat x (Word.Concat (NonterminalSubtree.frontier lower) z) ∧
      (x ≠ Word.Empty ∨ z ≠ Word.Empty) ∧
      Derives G [Symbol.nonterminal (NonterminalSubtree.root upper)]
        (SententialForm.terminalWord x ++
          [Symbol.nonterminal (NonterminalSubtree.root upper)] ++
          SententialForm.terminalWord z) := by
  cases upper with
  | mk A upperTree =>
  cases lower with
  | mk B lowerTree =>
  simp [NonterminalSubtree.root] at hroot
  cases hroot
  have hloop :=
    ParseTree.loop_derivation_from_repeated_selected_subtrees
      tree (Nat.le_of_lt hij) hupper hlower rfl
  cases hloop with
  | intro x hx =>
      cases hx with
      | intro z hz =>
          exists x
          exists z
          constructor
          · exact hz.left
          constructor
          · by_cases hxempty : x = Word.Empty
            · apply Or.inr
              intro hzempty
              have hinside :=
                ParseTree.later_selected_subtree_in_selected_subtree
                  tree (Nat.le_of_lt hij) hupper hlower
              have hpos : 0 < j - i := by lia
              have hlt :=
                ParseTree.selected_subtree_nodeCount_lt_of_pos_index
                  upperTree hpos hinside
              have hupperMinimal :=
                ParseTree.selected_subtree_minimal_for_frontier
                  tree hminimal hupper
              have hfrontUpper :
                  ParseTree.frontier upperTree =
                    Word.Concat x (Word.Concat (ParseTree.frontier lowerTree) z) := by
                simpa [NonterminalSubtree.frontier] using hz.left
              have hfrontEq :
                  ParseTree.frontier lowerTree = ParseTree.frontier upperTree := by
                rw [hfrontUpper, hxempty, hzempty]
                simp [Word.Concat, Word.Empty]
              have hle := hupperMinimal lowerTree hfrontEq
              simp [NonterminalSubtree.nodeCount] at hlt
              change ParseTree.nodeCount upperTree <=
                ParseTree.nodeCount lowerTree at hle
              lia
            · exact Or.inl hxempty
          · exact hz.right

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

/-!
Bounded production width controls frontier length exponentially in tree height.
Combining that bound with duplicate-subtree selection gives the small upper
subtree needed for finite pumping bounds.
-/

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

theorem ParseTree.height_gt_nonterminals_of_frontier_length_ge
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 1 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hlen :
      B ^ (G.nonterminalsFinite.elems.length + 1) <=
        Word.Length (ParseTree.frontier tree)) :
    G.nonterminalsFinite.elems.length < ParseTree.height tree := by
  by_cases hheight : G.nonterminalsFinite.elems.length < ParseTree.height tree
  · exact hheight
  have hheightLe :
      ParseTree.height tree <= G.nonterminalsFinite.elems.length := by
    lia
  have hFront :=
    ParseTree.frontier_length_le_pow (by lia : 0 < B) hBound tree
  have hPowLe :
      B ^ ParseTree.height tree <=
        B ^ G.nonterminalsFinite.elems.length :=
    Nat.pow_le_pow_right (by lia : 0 < B) hheightLe
  have hPowLt :
      B ^ G.nonterminalsFinite.elems.length <
        B ^ (G.nonterminalsFinite.elems.length + 1) := by
    rw [Nat.pow_succ]
    have hpos :
        0 < B ^ G.nonterminalsFinite.elems.length :=
      Nat.pow_pos (by lia : 0 < B)
    have hmul :
        B ^ G.nonterminalsFinite.elems.length * 1 <
          B ^ G.nonterminalsFinite.elems.length * B := by
      exact Nat.mul_lt_mul_of_pos_left hB hpos
    simpa using hmul
  have hFrontLt :
      Word.Length (ParseTree.frontier tree) <
        B ^ (G.nonterminalsFinite.elems.length + 1) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hFront hPowLe) hPowLt
  lia

theorem ParseTree.exists_duplicate_root_subtrees_near_bottom_frontier_bound
    [DecidableEq nonterminal]
    {G : CFG terminal nonterminal} {B : Nat}
    (hB : 0 < B)
    (hBound : forall A rhs, G.produces A rhs -> rhs.length < B)
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hheight : G.nonterminalsFinite.elems.length < ParseTree.height tree) :
    exists i j upper lower,
      i < j ∧
      j < ParseTree.height tree ∧
      (ParseTree.longestNonterminalSubtrees tree)[i]? = some upper ∧
      (ParseTree.longestNonterminalSubtrees tree)[j]? = some lower ∧
      NonterminalSubtree.root upper = NonterminalSubtree.root lower ∧
      NonterminalSubtree.height upper <=
        G.nonterminalsFinite.elems.length + 1 ∧
      Word.Length (NonterminalSubtree.frontier upper) <=
        B ^ (G.nonterminalsFinite.elems.length + 1) := by
  cases ParseTree.exists_duplicate_root_subtrees_near_bottom tree hheight with
  | intro i hi =>
      cases hi with
      | intro j hj =>
          cases hj with
          | intro upper hupper =>
              cases hupper with
              | intro lower hlower =>
                  have hFrontTree :=
                    ParseTree.frontier_length_le_pow hB hBound upper.2
                  have hPow :
                      B ^ NonterminalSubtree.height upper <=
                        B ^ (G.nonterminalsFinite.elems.length + 1) :=
                    Nat.pow_le_pow_right hB
                      hlower.right.right.right.right.right
                  exists i
                  exists j
                  exists upper
                  exists lower
                  constructor
                  · exact hlower.left
                  constructor
                  · exact hlower.right.left
                  constructor
                  · exact hlower.right.right.left
                  constructor
                  · exact hlower.right.right.right.left
                  constructor
                  · exact hlower.right.right.right.right.left
                  constructor
                  · exact hlower.right.right.right.right.right
                  · exact Nat.le_trans hFrontTree hPow

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

/-!
Leftmost and rightmost derivation traces give operational derivation orders.
The leftmost trace is tied back to parse trees, which lets the ambiguity
definition switch between distinct parse trees and distinct left derivations.
-/

def LeftmostYields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u v A rhs,
    SententialForm.allTerminals u ∧
      G.produces A rhs ∧
      x = u ++ [Symbol.nonterminal A] ++ v ∧
      y = u ++ rhs ++ v

def RightmostYields (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u v A rhs,
    SententialForm.allTerminals v ∧
      G.produces A rhs ∧
      x = u ++ [Symbol.nonterminal A] ++ v ∧
      y = u ++ rhs ++ v

theorem leftmostYields_yields {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : LeftmostYields G x y) : Yields G x y := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  exists u
                  exists v
                  exists A
                  exists rhs
                  exact And.intro hrhs.right.left hrhs.right.right

theorem rightmostYields_yields {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : RightmostYields G x y) : Yields G x y := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  exists u
                  exists v
                  exists A
                  exists rhs
                  exact And.intro hrhs.right.left hrhs.right.right

theorem leftmostYields_append_right {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : LeftmostYields G x y)
    (suffix : SententialForm terminal nonterminal) :
    LeftmostYields G (x ++ suffix) (y ++ suffix) := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  exists u
                  exists v ++ suffix
                  exists A
                  exists rhs
                  constructor
                  · exact hrhs.left
                  constructor
                  · exact hrhs.right.left
                  constructor
                  · rw [hrhs.right.right.left]
                    simp [List.append_assoc]
                  · rw [hrhs.right.right.right]
                    simp [List.append_assoc]

theorem leftmostYields_append_left_of_allTerminals
    {G : CFG terminal nonterminal}
    {x y pref : SententialForm terminal nonterminal}
    (hpref : SententialForm.allTerminals pref)
    (h : LeftmostYields G x y) :
    LeftmostYields G (pref ++ x) (pref ++ y) := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  exists pref ++ u
                  exists v
                  exists A
                  exists rhs
                  constructor
                  · exact SententialForm.allTerminals_append_of hpref hrhs.left
                  constructor
                  · exact hrhs.right.left
                  constructor
                  · rw [hrhs.right.right.left]
                    simp [List.append_assoc]
                  · rw [hrhs.right.right.right]
                    simp [List.append_assoc]

/-
Leftmost and rightmost derivation traces make the deterministic choice of a
rewrite position explicit. The trace constructors are later related back to
ordinary derivations and to parse-tree construction.
-/

inductive LeftDerivationTrace (G : CFG terminal nonterminal) :
    SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Type where
  | refl (x : SententialForm terminal nonterminal) :
      LeftDerivationTrace G x x
  | step {x y z : SententialForm terminal nonterminal} :
      LeftmostYields G x y ->
        LeftDerivationTrace G y z -> LeftDerivationTrace G x z

inductive RightDerivationTrace (G : CFG terminal nonterminal) :
    SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Type where
  | refl (x : SententialForm terminal nonterminal) :
      RightDerivationTrace G x x
  | step {x y z : SententialForm terminal nonterminal} :
      RightmostYields G x y ->
        RightDerivationTrace G y z -> RightDerivationTrace G x z

def LeftDerives (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  Nonempty (LeftDerivationTrace G x y)

def RightDerives (G : CFG terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  Nonempty (RightDerivationTrace G x y)

namespace LeftDerivationTrace

def trans {G : CFG terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : LeftDerivationTrace G x y)
    (hyz : LeftDerivationTrace G y z) :
    LeftDerivationTrace G x z :=
  match hxy with
  | refl _ => hyz
  | step hstep hrest => step hstep (trans hrest hyz)

def appendRight {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : LeftDerivationTrace G x y)
    (suffix : SententialForm terminal nonterminal) :
    LeftDerivationTrace G (x ++ suffix) (y ++ suffix) :=
  match h with
  | refl _ => refl _
  | step hstep hrest =>
      step (leftmostYields_append_right hstep suffix)
        (appendRight hrest suffix)

def appendLeftTerminals {G : CFG terminal nonterminal}
    {x y pref : SententialForm terminal nonterminal}
    (hpref : SententialForm.allTerminals pref)
    (h : LeftDerivationTrace G x y) :
    LeftDerivationTrace G (pref ++ x) (pref ++ y) :=
  match h with
  | refl _ => refl _
  | step hstep hrest =>
      step (leftmostYields_append_left_of_allTerminals hpref hstep)
        (appendLeftTerminals hpref hrest)

theorem toDerives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : LeftDerivationTrace G x y) : Derives G x y := by
  induction h with
  | refl x =>
      exact Derives.refl x
  | step hstep _ ih =>
      exact Derives.step (leftmostYields_yields hstep) ih

def castTarget {G : CFG terminal nonterminal}
    {x y y' : SententialForm terminal nonterminal}
    (h : y = y') (d : LeftDerivationTrace G x y) :
    LeftDerivationTrace G x y' :=
  h ▸ d

/-
The states of a trace list every sentential form along the derivation, from
the source through each rewrite down to the target. In the book, a left
derivation is exactly this sequence of sentential forms; because the step
obligations are propositions, traces with equal state lists are equal, so
comparing traces is the same as comparing derivations in the book's sense.
-/

def states {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d : LeftDerivationTrace G x y) :
    List (SententialForm terminal nonterminal) :=
  match x, y, d with
  | _, _, refl a => [a]
  | x, _, step _ rest => x :: states rest

theorem states_ne_nil {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d : LeftDerivationTrace G x y) : d.states ≠ [] := by
  cases d with
  | refl a => simp [states]
  | step hstep rest => simp [states]

theorem states_head? {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d : LeftDerivationTrace G x y) : d.states.head? = some x := by
  cases d with
  | refl a => rfl
  | step hstep rest => rfl

theorem states_castTarget {G : CFG terminal nonterminal}
    {x y y' : SententialForm terminal nonterminal}
    (h : y = y') (d : LeftDerivationTrace G x y) :
    (castTarget h d).states = d.states := by
  cases h
  rfl

theorem states_trans {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d1 : LeftDerivationTrace G x y) :
    forall {z : SententialForm terminal nonterminal}
      (d2 : LeftDerivationTrace G y z),
      (d1.trans d2).states = d1.states.dropLast ++ d2.states := by
  induction d1 with
  | refl a =>
      intro z d2
      simp [trans, states]
  | step hstep rest ih =>
      intro z d2
      simp only [trans, states, ih, List.cons_append,
        List.dropLast_cons_of_ne_nil (states_ne_nil rest)]

theorem states_appendRight {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d : LeftDerivationTrace G x y)
    (suffix : SententialForm terminal nonterminal) :
    (d.appendRight suffix).states = d.states.map (· ++ suffix) := by
  induction d with
  | refl a => rfl
  | step hstep rest ih =>
      simp only [appendRight, states, ih, List.map_cons]

theorem states_appendLeftTerminals {G : CFG terminal nonterminal}
    {x y pref : SententialForm terminal nonterminal}
    (hpref : SententialForm.allTerminals pref)
    (d : LeftDerivationTrace G x y) :
    (d.appendLeftTerminals hpref).states = d.states.map (pref ++ ·) := by
  induction d with
  | refl a => rfl
  | step hstep rest ih =>
      simp only [appendLeftTerminals, states, ih, List.map_cons]

theorem eq_of_states_eq {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (d1 : LeftDerivationTrace G x y) :
    forall d2 : LeftDerivationTrace G x y,
      d1.states = d2.states -> d1 = d2 := by
  induction d1 with
  | refl a =>
      intro d2 h
      cases d2 with
      | refl _ => rfl
      | step hstep2 rest2 =>
          exfalso
          simp only [states] at h
          injection h with _ htail
          exact states_ne_nil rest2 htail.symm
  | step hstep1 rest1 ih =>
      intro d2 h
      cases d2 with
      | refl _ =>
          exfalso
          simp only [states] at h
          injection h with _ htail
          exact states_ne_nil rest1 htail
      | step hstep2 rest2 =>
          simp only [states] at h
          injection h with _ htail
          have hmid := states_head? rest1
          rw [htail, states_head? rest2] at hmid
          injection hmid with hmid
          subst hmid
          rw [ih rest2 htail]

end LeftDerivationTrace

namespace RightDerivationTrace

theorem toDerives {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : RightDerivationTrace G x y) : Derives G x y := by
  induction h with
  | refl x =>
      exact Derives.refl x
  | step hstep _ ih =>
      exact Derives.step (rightmostYields_yields hstep) ih

end RightDerivationTrace

mutual

/-
Every parse tree induces a left derivation by expanding the root production and
then processing the forest from left to right. This is the direction needed to
compare ambiguity by parse trees with ambiguity by left derivations. The
definitions are given by explicit trace combinators, with a single target cast
per forest node, so the state sequence of the resulting trace can be computed
by the lemmas that follow.
-/

def ParseTree.leftDerivationTrace {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    LeftDerivationTrace G [s]
      (SententialForm.terminalWord (ParseTree.frontier tree)) :=
  match tree with
  | ParseTree.leaf _ =>
      LeftDerivationTrace.refl _
  | ParseTree.node A rhs hprod children =>
      LeftDerivationTrace.step
        (x := [Symbol.nonterminal A]) (y := rhs)
        ⟨[], [], A, rhs, trivial, hprod, rfl, by simp⟩
        (ParseForest.leftDerivationTrace children)

def ParseForest.leftDerivationTrace {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    LeftDerivationTrace G sent
      (SententialForm.terminalWord (ParseForest.frontier forest)) :=
  match forest with
  | ParseForest.nil =>
      LeftDerivationTrace.refl _
  | ParseForest.cons _ restSent tree rest =>
      LeftDerivationTrace.castTarget
        (SententialForm.terminalWord_append
          (ParseTree.frontier tree) (ParseForest.frontier rest)).symm
        (LeftDerivationTrace.trans
          ((ParseTree.leftDerivationTrace tree).appendRight restSent)
          ((ParseForest.leftDerivationTrace rest).appendLeftTerminals
            (SententialForm.terminalWord_allTerminals
              (ParseTree.frontier tree))))

end

theorem leftDerivationTrace_to_parseForest_terminal
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} {w : Word terminal}
    (h : LeftDerivationTrace G sent (SententialForm.terminalWord w)) :
    exists forest : ParseForest G sent, ParseForest.frontier forest = w :=
  ParseForest.of_derives_terminal (LeftDerivationTrace.toDerives h)

theorem parseTree_leftDerivationTrace_correspondence
    {G : CFG terminal nonterminal} {w : Word terminal} :
    (exists tree : ParseTree G (Symbol.nonterminal G.start),
      ParseTree.frontier tree = w) <->
    Nonempty
      (LeftDerivationTrace G [Symbol.nonterminal G.start]
        (SententialForm.terminalWord w)) := by
  constructor
  · intro h
    cases h with
    | intro tree hfront =>
        constructor
        rw [← hfront]
        exact ParseTree.leftDerivationTrace tree
  · intro h
    cases h with
    | intro trace =>
        cases leftDerivationTrace_to_parseForest_terminal trace with
        | intro forest hfront =>
            cases forest with
            | cons _ _ tree rest =>
                cases rest with
                | nil =>
                    exists tree
                    simpa [ParseForest.frontier, Word.Concat] using hfront

/-!
# Left derivations and ambiguity

The rest of the module proves the book's Theorem 4.5: parse trees rooted at a
symbol and leftmost derivation traces of a terminal word correspond one to
one. A left derivation is compared through its state sequence, the list of
sentential forms it passes through, which matches the book's reading of a
derivation. The correspondence then shows that ambiguity by parse trees
coincides with ambiguity by left derivations, where the left derivations
themselves are required to differ, not merely the parse trees they came from.
-/

private theorem list_dropLast_append_getLast? {alpha : Type u}
    {l : List alpha} {a : alpha} (h : l.getLast? = some a) :
    l.dropLast ++ [a] = l := by
  induction l with
  | nil => cases h
  | cons b t ih =>
      cases t with
      | nil =>
          have hb : ([b] : List alpha).getLast? = some b := rfl
          rw [hb] at h
          injection h with h
          rw [← h]
          rfl
      | cons c t' =>
          rw [List.getLast?_cons_cons] at h
          show b :: ((c :: t').dropLast ++ [a]) = b :: (c :: t')
          rw [ih h]

mutual

/-
The state sequence of the canonical left derivation of a tree or forest,
computed structurally: a node contributes its root expansion, and a forest
first rewrites its head tree with the remaining sentential form appended and
then rewrites the remaining forest behind the head tree's terminal frontier.
-/

def ParseTree.leftStates {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} :
    ParseTree G s -> List (SententialForm terminal nonterminal)
  | ParseTree.leaf a => [[Symbol.terminal a]]
  | ParseTree.node A _ _ children =>
      [Symbol.nonterminal A] :: ParseForest.leftStates children

def ParseForest.leftStates {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} :
    ParseForest G sent -> List (SententialForm terminal nonterminal)
  | ParseForest.nil => [[]]
  | ParseForest.cons _ restSent tree rest =>
      (ParseTree.leftStates tree).dropLast.map (· ++ restSent) ++
        (ParseForest.leftStates rest).map
          (SententialForm.terminalWord (ParseTree.frontier tree) ++ ·)

end

mutual

theorem ParseTree.states_leftDerivationTrace {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    (ParseTree.leftDerivationTrace tree).states = ParseTree.leftStates tree := by
  cases tree with
  | leaf a => rfl
  | node A rhs hprod children =>
      have hChildren := ParseForest.states_leftDerivationTrace children
      simp only [ParseTree.leftDerivationTrace, ParseTree.leftStates,
        LeftDerivationTrace.states]
      exact congrArg ([Symbol.nonterminal A] :: ·) hChildren

theorem ParseForest.states_leftDerivationTrace {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    (ParseForest.leftDerivationTrace forest).states =
      ParseForest.leftStates forest := by
  cases forest with
  | nil => rfl
  | cons s restSent tree rest =>
      have hTree := ParseTree.states_leftDerivationTrace tree
      have hRest := ParseForest.states_leftDerivationTrace rest
      calc (ParseForest.leftDerivationTrace
              (ParseForest.cons s restSent tree rest)).states
          = ((ParseTree.leftDerivationTrace tree).appendRight
                restSent).states.dropLast ++
              ((ParseForest.leftDerivationTrace rest).appendLeftTerminals
                (SententialForm.terminalWord_allTerminals
                  (ParseTree.frontier tree))).states :=
            (LeftDerivationTrace.states_castTarget _ _).trans
              (LeftDerivationTrace.states_trans _ _)
        _ = ((ParseTree.leftStates tree).map (· ++ restSent)).dropLast ++
              (ParseForest.leftStates rest).map
                (SententialForm.terminalWord (ParseTree.frontier tree) ++ ·) := by
            rw [LeftDerivationTrace.states_appendRight,
              LeftDerivationTrace.states_appendLeftTerminals, hTree, hRest]
        _ = ParseForest.leftStates (ParseForest.cons s restSent tree rest) := by
            simp only [ParseForest.leftStates, List.map_dropLast]

end

theorem ParseTree.leftStates_ne_nil {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    ParseTree.leftStates tree ≠ [] := by
  cases tree with
  | leaf a => simp [ParseTree.leftStates]
  | node A rhs hprod children => simp [ParseTree.leftStates]

theorem ParseForest.leftStates_ne_nil {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    ParseForest.leftStates forest ≠ [] := by
  cases forest with
  | nil => simp [ParseForest.leftStates]
  | cons s restSent tree rest =>
      intro h
      simp only [ParseForest.leftStates] at h
      rcases List.append_eq_nil_iff.mp h with ⟨-, hmap⟩
      exact ParseForest.leftStates_ne_nil rest (List.map_eq_nil_iff.mp hmap)

theorem ParseForest.leftStates_getLast? {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    (ParseForest.leftStates forest).getLast? =
      some (SententialForm.terminalWord (ParseForest.frontier forest)) := by
  cases forest with
  | nil => rfl
  | cons s restSent tree rest =>
      have hRest := ParseForest.leftStates_getLast? rest
      simp [ParseForest.leftStates, ParseForest.frontier, List.getLast?_append,
        List.getLast?_map, hRest, SententialForm.terminalWord_append]

theorem ParseTree.leftStates_getLast? {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    (ParseTree.leftStates tree).getLast? =
      some (SententialForm.terminalWord (ParseTree.frontier tree)) := by
  cases tree with
  | leaf a => rfl
  | node A rhs hprod children =>
      have hChildren := ParseForest.leftStates_getLast? children
      simp [ParseTree.leftStates, ParseTree.frontier, List.getLast?_cons,
        hChildren]

theorem ParseForest.leftStates_head? {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    (ParseForest.leftStates forest).head? = some sent := by
  cases forest with
  | nil => rfl
  | cons s restSent tree rest =>
      cases tree with
      | leaf a =>
          have hRest := ParseForest.leftStates_head? rest
          simp [ParseForest.leftStates, ParseTree.leftStates, ParseTree.frontier,
            List.head?_map, hRest, SententialForm.terminalWord]
      | node A rhs hprod children =>
          have hne := ParseForest.leftStates_ne_nil children
          simp [ParseForest.leftStates, ParseTree.leftStates,
            List.dropLast_cons_of_ne_nil hne]

/-
A one-tree forest performs exactly the derivation of its tree: the trailing
empty sentential form contributes nothing, and the final state of the tree
derivation is its terminal frontier.
-/

theorem ParseForest.leftStates_singleton {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    ParseForest.leftStates (ParseForest.cons s [] tree ParseForest.nil) =
      ParseTree.leftStates tree := by
  have hlast := ParseTree.leftStates_getLast? tree
  simp only [ParseForest.leftStates]
  simp
  exact list_dropLast_append_getLast? hlast

/-
Forests over an all-terminal sentential form are forced: every tree must be a
leaf. Their frontier reads back the sentential form and their derivation is a
single state.
-/

theorem ParseForest.eq_of_allTerminals {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal}
    (hsent : SententialForm.allTerminals sent)
    (f1 f2 : ParseForest G sent) : f1 = f2 := by
  cases f1 with
  | nil =>
      cases f2 with
      | nil => rfl
  | cons s restSent t1 r1 =>
      cases f2 with
      | cons _ _ t2 r2 =>
          cases s with
          | terminal a =>
              cases t1 with
              | leaf _ =>
                  cases t2 with
                  | leaf _ =>
                      have hrest : SententialForm.allTerminals restSent := hsent
                      rw [ParseForest.eq_of_allTerminals hrest r1 r2]
          | nonterminal A => cases hsent

theorem ParseForest.leftStates_of_allTerminals {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal}
    (hsent : SententialForm.allTerminals sent)
    (f : ParseForest G sent) :
    ParseForest.leftStates f = [sent] := by
  cases f with
  | nil => rfl
  | cons s restSent tree rest =>
      cases s with
      | terminal a =>
          cases tree with
          | leaf _ =>
              have hrest : SententialForm.allTerminals restSent := hsent
              simp [ParseForest.leftStates, ParseTree.leftStates,
                ParseTree.frontier, SententialForm.terminalWord,
                ParseForest.leftStates_of_allTerminals hrest rest]
      | nonterminal A => cases hsent

theorem ParseForest.terminalWord_frontier_of_allTerminals
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal}
    (hsent : SententialForm.allTerminals sent)
    (f : ParseForest G sent) :
    SententialForm.terminalWord (ParseForest.frontier f) = sent := by
  cases f with
  | nil => rfl
  | cons s restSent tree rest =>
      cases s with
      | terminal a =>
          cases tree with
          | leaf _ =>
              have hrest : SententialForm.allTerminals restSent := hsent
              have hone : SententialForm.terminalWord (nt := nonterminal) [a] =
                  [Symbol.terminal a] := rfl
              simp [ParseForest.frontier, ParseTree.frontier,
                SententialForm.terminalWord_append, hone,
                ParseForest.terminalWord_frontier_of_allTerminals hrest rest]
      | nonterminal A => cases hsent

theorem ParseForest.nonempty_of_allTerminals {G : CFG terminal nonterminal} :
    forall (sent : SententialForm terminal nonterminal),
      SententialForm.allTerminals sent -> Nonempty (ParseForest G sent) := by
  intro sent
  induction sent with
  | nil =>
      intro _
      exact ⟨ParseForest.nil⟩
  | cons s rest ih =>
      intro h
      cases s with
      | terminal a =>
          have hrest : SententialForm.allTerminals rest := h
          cases ih hrest with
          | intro f =>
              exact ⟨ParseForest.cons _ _ (ParseTree.leaf a) f⟩
      | nonterminal A => cases h

/-
Splitting and joining forests along an append of sentential forms. Splits
exist and appends are injective because a forest follows the list structure of
its sentential form exactly.
-/

theorem ParseForest.exists_append_eq {G : CFG terminal nonterminal} :
    forall {left : SententialForm terminal nonterminal}
      {right : SententialForm terminal nonterminal}
      (f : ParseForest G (left ++ right)),
      exists leftForest : ParseForest G left,
        exists rightForest : ParseForest G right,
          f = ParseForest.append leftForest rightForest := by
  intro left
  induction left with
  | nil =>
      intro right f
      exact ⟨ParseForest.nil, f, rfl⟩
  | cons s rest ih =>
      intro right f
      cases f with
      | cons _ _ tree fr =>
          cases ih fr with
          | intro f1 hf1 =>
              cases hf1 with
              | intro f2 heq =>
                  refine ⟨ParseForest.cons s rest tree f1, f2, ?_⟩
                  rw [heq]
                  rfl

theorem ParseForest.append_inj {G : CFG terminal nonterminal} :
    forall {left : SententialForm terminal nonterminal}
      {right : SententialForm terminal nonterminal}
      {f1 g1 : ParseForest G left} {f2 g2 : ParseForest G right},
      ParseForest.append f1 f2 = ParseForest.append g1 g2 ->
        f1 = g1 ∧ f2 = g2 := by
  intro left
  induction left with
  | nil =>
      intro right f1 g1 f2 g2 h
      cases f1
      cases g1
      exact ⟨rfl, h⟩
  | cons s rest ih =>
      intro right f1 g1 f2 g2 h
      cases f1 with
      | cons _ _ t1 r1 =>
          cases g1 with
          | cons _ _ t2 r2 =>
              injection h with _ _ ht hr
              cases ih hr with
              | intro hrest happend =>
                  refine ⟨?_, happend⟩
                  rw [ht, hrest]

/-
The general append law for derivation states: an appended forest first runs
the left derivation of the left part in front of the right sentential form,
then runs the right derivation behind the left part's terminal frontier.
-/

theorem ParseForest.leftStates_append {G : CFG terminal nonterminal} :
    forall {left : SententialForm terminal nonterminal}
      {right : SententialForm terminal nonterminal}
      (f : ParseForest G left) (g : ParseForest G right),
      ParseForest.leftStates (ParseForest.append f g) =
        (ParseForest.leftStates f).dropLast.map (· ++ right) ++
          (ParseForest.leftStates g).map
            (SententialForm.terminalWord (ParseForest.frontier f) ++ ·) := by
  intro left right f g
  cases f with
  | nil =>
      simp [ParseForest.append, ParseForest.leftStates, ParseForest.frontier,
        SententialForm.terminalWord]
  | cons s restSent tree rest =>
      have ih := ParseForest.leftStates_append rest g
      have hne : (ParseForest.leftStates rest).map
          (SententialForm.terminalWord (ParseTree.frontier tree) ++ ·) ≠ [] := by
        intro hmap
        exact ParseForest.leftStates_ne_nil rest (List.map_eq_nil_iff.mp hmap)
      simp [ParseForest.append, ParseForest.leftStates, ih,
        List.dropLast_append_of_ne_nil hne, ParseForest.frontier,
        SententialForm.terminalWord_append, List.map_map, Function.comp_def,
        List.append_assoc, ← List.map_dropLast]

theorem ParseForest.leftStates_append_of_allTerminals
    {G : CFG terminal nonterminal}
    {left right : SententialForm terminal nonterminal}
    (hleft : SententialForm.allTerminals left)
    (f : ParseForest G left) (g : ParseForest G right) :
    ParseForest.leftStates (ParseForest.append f g) =
      (ParseForest.leftStates g).map (left ++ ·) := by
  rw [ParseForest.leftStates_append,
    ParseForest.leftStates_of_allTerminals hleft f,
    ParseForest.terminalWord_frontier_of_allTerminals hleft f]
  rfl

/-
The expansion step: a forest whose sentential form is an all-terminal prefix,
a nonterminal, and a suffix performs the leftmost rewrite of that nonterminal
first, and afterwards behaves as the forest with the node replaced by its
children. This is the forest reading of one leftmost derivation step.
-/

theorem ParseForest.leftStates_expand {G : CFG terminal nonterminal}
    {u v rhs : SententialForm terminal nonterminal} {A : nonterminal}
    (hu : SententialForm.allTerminals u)
    (fu : ParseForest G u) (hprod : G.produces A rhs)
    (children : ParseForest G rhs) (fv : ParseForest G v) :
    ParseForest.leftStates
        (ParseForest.append
          (ParseForest.append fu
            (ParseForest.cons (Symbol.nonterminal A) []
              (ParseTree.node A rhs hprod children) ParseForest.nil))
          fv) =
      (u ++ [Symbol.nonterminal A] ++ v) ::
        ParseForest.leftStates
          (ParseForest.append (ParseForest.append fu children) fv) := by
  have hmap_ne : (ParseForest.leftStates children).map (u ++ ·) ≠ [] := by
    intro hmap
    exact ParseForest.leftStates_ne_nil children (List.map_eq_nil_iff.mp hmap)
  have hfront2 : SententialForm.terminalWord (nt := nonterminal)
      (ParseForest.frontier (ParseForest.append fu
        (ParseForest.cons (Symbol.nonterminal A) []
          (ParseTree.node A rhs hprod children) ParseForest.nil))) =
      SententialForm.terminalWord
        (ParseForest.frontier (ParseForest.append fu children)) := by
    simp [ParseForest.frontier_append, ParseForest.frontier, ParseTree.frontier,
      Word.Concat]
  rw [ParseForest.leftStates_append (ParseForest.append fu
      (ParseForest.cons (Symbol.nonterminal A) []
        (ParseTree.node A rhs hprod children) ParseForest.nil)) fv,
    ParseForest.leftStates_append (ParseForest.append fu children) fv,
    ParseForest.leftStates_append_of_allTerminals hu fu,
    ParseForest.leftStates_append_of_allTerminals hu fu,
    ParseForest.leftStates_singleton, hfront2]
  simp only [ParseTree.leftStates, List.map_cons,
    List.dropLast_cons_of_ne_nil hmap_ne, List.cons_append]

/-
Theorem 4.5, forest form. Every leftmost derivation trace of a terminal word
is the canonical derivation of exactly one parse forest: the state sequence of
a trace determines the forest, and every trace's state sequence is realized.
-/

theorem LeftDerivationTrace.exists_forest_states_eq
    {G : CFG terminal nonterminal}
    {sent target : SententialForm terminal nonterminal}
    (d : LeftDerivationTrace G sent target) :
    SententialForm.allTerminals target ->
      exists f : ParseForest G sent,
        SententialForm.terminalWord (ParseForest.frontier f) = target ∧
        ParseForest.leftStates f = d.states := by
  induction d with
  | refl x =>
      intro htarget
      cases ParseForest.nonempty_of_allTerminals (G := G) x htarget with
      | intro f =>
          exact ⟨f, ParseForest.terminalWord_frontier_of_allTerminals htarget f,
            ParseForest.leftStates_of_allTerminals htarget f⟩
  | step hstep rest ih =>
      intro htarget
      rcases ih htarget with ⟨fy, hfy_front, hfy_states⟩
      rcases hstep with ⟨u, v, A, rhs, hu, hprod, hx, hy⟩
      subst hx
      subst hy
      rcases ParseForest.exists_append_eq fy with ⟨fl, fv, hfl⟩
      rcases ParseForest.exists_append_eq fl with ⟨fu, frhs, hfu⟩
      subst hfl
      subst hfu
      refine ⟨ParseForest.append
        (ParseForest.append fu
          (ParseForest.cons (Symbol.nonterminal A) []
            (ParseTree.node A rhs hprod frhs) ParseForest.nil)) fv, ?_, ?_⟩
      · rw [← hfy_front]
        simp [ParseForest.frontier_append, ParseForest.frontier,
          ParseTree.frontier, Word.Concat, List.append_assoc]
      · rw [ParseForest.leftStates_expand hu fu hprod frhs fv, hfy_states]
        rfl

theorem LeftDerivationTrace.forest_unique_of_states_eq
    {G : CFG terminal nonterminal}
    {sent target : SententialForm terminal nonterminal}
    (d : LeftDerivationTrace G sent target) :
    SententialForm.allTerminals target ->
      forall (f1 f2 : ParseForest G sent),
        ParseForest.leftStates f1 = d.states ->
        ParseForest.leftStates f2 = d.states -> f1 = f2 := by
  induction d with
  | refl x =>
      intro htarget f1 f2 _ _
      exact ParseForest.eq_of_allTerminals htarget f1 f2
  | step hstep rest ih =>
      intro htarget f1 f2 h1 h2
      rcases hstep with ⟨u, v, A, rhs, hu, hprod, hx, hy⟩
      subst hx
      subst hy
      rcases ParseForest.exists_append_eq f1 with ⟨fl1, fv1, hfl1⟩
      rcases ParseForest.exists_append_eq fl1 with ⟨fu1, fn1, hfn1⟩
      subst hfl1
      subst hfn1
      rcases ParseForest.exists_append_eq f2 with ⟨fl2, fv2, hfl2⟩
      rcases ParseForest.exists_append_eq fl2 with ⟨fu2, fn2, hfn2⟩
      subst hfl2
      subst hfn2
      cases fn1 with
      | cons _ _ T1 rest1 =>
          cases rest1 with
          | nil =>
              cases T1 with
              | node _ rhs1 hprod1 ch1 =>
                  cases fn2 with
                  | cons _ _ T2 rest2 =>
                      cases rest2 with
                      | nil =>
                          cases T2 with
                          | node _ rhs2 hprod2 ch2 =>
                              rw [ParseForest.leftStates_expand hu fu1 hprod1 ch1 fv1] at h1
                              rw [ParseForest.leftStates_expand hu fu2 hprod2 ch2 fv2] at h2
                              simp only [LeftDerivationTrace.states] at h1 h2
                              injection h1 with _ h1
                              injection h2 with _ h2
                              have hhead1 := ParseForest.leftStates_head?
                                (ParseForest.append (ParseForest.append fu1 ch1) fv1)
                              rw [h1, LeftDerivationTrace.states_head? rest] at hhead1
                              injection hhead1 with hhead1
                              have hrhs1 : rhs1 = rhs :=
                                (List.append_cancel_left
                                  (List.append_cancel_right hhead1)).symm
                              have hhead2 := ParseForest.leftStates_head?
                                (ParseForest.append (ParseForest.append fu2 ch2) fv2)
                              rw [h2, LeftDerivationTrace.states_head? rest] at hhead2
                              injection hhead2 with hhead2
                              have hrhs2 : rhs2 = rhs :=
                                (List.append_cancel_left
                                  (List.append_cancel_right hhead2)).symm
                              subst hrhs1
                              subst hrhs2
                              have hforest := ih htarget
                                (ParseForest.append (ParseForest.append fu1 ch1) fv1)
                                (ParseForest.append (ParseForest.append fu2 ch2) fv2)
                                h1 h2
                              cases ParseForest.append_inj hforest with
                              | intro hl hv =>
                                  cases ParseForest.append_inj hl with
                                  | intro hfu hch =>
                                      rw [hfu, hch, hv]

theorem ParseTree.eq_of_leftStates_eq {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} {t1 t2 : ParseTree G s}
    (h : ParseTree.leftStates t1 = ParseTree.leftStates t2) : t1 = t2 := by
  have h1 : ParseForest.leftStates (ParseForest.cons s [] t1 ParseForest.nil) =
      (ParseForest.leftDerivationTrace
        (ParseForest.cons s [] t1 ParseForest.nil)).states := by
    rw [ParseForest.states_leftDerivationTrace]
  have h2 : ParseForest.leftStates (ParseForest.cons s [] t2 ParseForest.nil) =
      (ParseForest.leftDerivationTrace
        (ParseForest.cons s [] t1 ParseForest.nil)).states := by
    rw [ParseForest.states_leftDerivationTrace, ParseForest.leftStates_singleton,
      ParseForest.leftStates_singleton]
    exact h.symm
  have hforest :=
    LeftDerivationTrace.forest_unique_of_states_eq
      (ParseForest.leftDerivationTrace
        (ParseForest.cons s [] t1 ParseForest.nil))
      (SententialForm.terminalWord_allTerminals _) _ _ h1 h2
  injection hforest

/-
Theorem 4.5, tree form. Fixing the derived word, a parse tree with that
frontier determines a leftmost derivation trace of the word, the assignment is
injective, and every trace arises from exactly one such tree.
-/

def ParseTree.leftDerivationTraceTo {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} {w : Word terminal}
    (tree : ParseTree G s) (hfrontier : ParseTree.frontier tree = w) :
    LeftDerivationTrace G [s] (SententialForm.terminalWord w) :=
  LeftDerivationTrace.castTarget
    (congrArg (SententialForm.terminalWord (nt := nonterminal)) hfrontier)
    (ParseTree.leftDerivationTrace tree)

theorem ParseTree.states_leftDerivationTraceTo {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} {w : Word terminal}
    (tree : ParseTree G s) (hfrontier : ParseTree.frontier tree = w) :
    (ParseTree.leftDerivationTraceTo tree hfrontier).states =
      ParseTree.leftStates tree :=
  (LeftDerivationTrace.states_castTarget _ _).trans
    (ParseTree.states_leftDerivationTrace tree)

theorem ParseTree.leftDerivationTraceTo_inj {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} {w : Word terminal}
    {t1 t2 : ParseTree G s}
    {h1 : ParseTree.frontier t1 = w} {h2 : ParseTree.frontier t2 = w}
    (heq : ParseTree.leftDerivationTraceTo t1 h1 =
      ParseTree.leftDerivationTraceTo t2 h2) :
    t1 = t2 := by
  apply ParseTree.eq_of_leftStates_eq
  rw [← ParseTree.states_leftDerivationTraceTo t1 h1,
    ← ParseTree.states_leftDerivationTraceTo t2 h2, heq]

theorem exists_unique_parseTree_of_leftDerivationTrace
    {G : CFG terminal nonterminal} {w : Word terminal}
    (d : LeftDerivationTrace G [Symbol.nonterminal G.start]
      (SententialForm.terminalWord w)) :
    exists tree : ParseTree G (Symbol.nonterminal G.start),
      (exists hfrontier : ParseTree.frontier tree = w,
        ParseTree.leftDerivationTraceTo tree hfrontier = d) ∧
      forall (tree' : ParseTree G (Symbol.nonterminal G.start))
        (hfrontier' : ParseTree.frontier tree' = w),
        ParseTree.leftDerivationTraceTo tree' hfrontier' = d -> tree' = tree := by
  rcases LeftDerivationTrace.exists_forest_states_eq d
    (SententialForm.terminalWord_allTerminals w) with ⟨f, hfront, hstates⟩
  cases f with
  | cons _ _ tree rest =>
      cases rest with
      | nil =>
          have hfrontier : ParseTree.frontier tree = w := by
            have htoWord := congrArg SententialForm.toWord? hfront
            rw [SententialForm.terminalWord_toWord,
              SententialForm.terminalWord_toWord] at htoWord
            injection htoWord with htoWord
            simpa [ParseForest.frontier, ParseTree.frontier, Word.Concat]
              using htoWord
          have hstates_tree : ParseTree.leftStates tree = d.states := by
            rw [← ParseForest.leftStates_singleton tree]
            exact hstates
          refine ⟨tree, ⟨hfrontier, ?_⟩, ?_⟩
          · apply LeftDerivationTrace.eq_of_states_eq
            rw [ParseTree.states_leftDerivationTraceTo, hstates_tree]
          · intro tree' hfrontier' htrace'
            apply ParseTree.eq_of_leftStates_eq
            rw [← ParseTree.states_leftDerivationTraceTo tree' hfrontier',
              htrace', ← hstates_tree]

/-!
Ambiguity by left derivations asks for two genuinely different left
derivations of the same word: two traces from the start symbol that differ,
which by the state-sequence lemma above means traces passing through
different sequences of sentential forms. Theorem 4.5 turns this into the
parse-tree reading and back.
-/

def AmbiguousByLeftDerivations (G : CFG terminal nonterminal) : Prop :=
  exists w : Word terminal,
    exists d1 : LeftDerivationTrace G [Symbol.nonterminal G.start]
        (SententialForm.terminalWord w),
      exists d2 : LeftDerivationTrace G [Symbol.nonterminal G.start]
          (SententialForm.terminalWord w),
        d1 ≠ d2

def AmbiguousByParseTrees (G : CFG terminal nonterminal) : Prop :=
  exists w, exists t1 : ParseTree G (Symbol.nonterminal G.start),
    exists t2 : ParseTree G (Symbol.nonterminal G.start),
      ParseTree.frontier t1 = w ∧
      ParseTree.frontier t2 = w ∧
      t1 ≠ t2

theorem ambiguousByParseTrees_iff_leftDerivations
    (G : CFG terminal nonterminal) :
    AmbiguousByParseTrees G <-> AmbiguousByLeftDerivations G := by
  constructor
  · intro h
    rcases h with ⟨w, t1, t2, hf1, hf2, hne⟩
    refine ⟨w, ParseTree.leftDerivationTraceTo t1 hf1,
      ParseTree.leftDerivationTraceTo t2 hf2, ?_⟩
    intro heq
    exact hne (ParseTree.leftDerivationTraceTo_inj heq)
  · intro h
    rcases h with ⟨w, d1, d2, hne⟩
    rcases exists_unique_parseTree_of_leftDerivationTrace d1 with
      ⟨t1, ⟨hf1, ht1⟩, -⟩
    rcases exists_unique_parseTree_of_leftDerivationTrace d2 with
      ⟨t2, ⟨hf2, ht2⟩, -⟩
    refine ⟨w, t1, t2, hf1, hf2, ?_⟩
    intro heq
    apply hne
    rw [← ht1, ← ht2]
    subst heq
    rfl

end CFG

end Grammars
end FoC

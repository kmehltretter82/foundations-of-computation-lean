import FoC.Grammars.ParseTreePart1

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
              have hpos : 0 < j - i := by omega
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
              omega
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
    omega
  have hsuffixLong :
      G.nonterminalsFinite.elems.length < suffix.length := by
    rw [hsuffixLen]
    omega
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
                      · omega
                      constructor
                      · have hqLen : q < suffix.length := hA.right.left
                        rw [hsuffixLen] at hqLen
                        simp [offset]
                        omega
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
                        omega

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
    omega
  have hFront :=
    ParseTree.frontier_length_le_pow (by omega : 0 < B) hBound tree
  have hPowLe :
      B ^ ParseTree.height tree <=
        B ^ G.nonterminalsFinite.elems.length :=
    Nat.pow_le_pow_right (by omega : 0 < B) hheightLe
  have hPowLt :
      B ^ G.nonterminalsFinite.elems.length <
        B ^ (G.nonterminalsFinite.elems.length + 1) := by
    rw [Nat.pow_succ]
    have hpos :
        0 < B ^ G.nonterminalsFinite.elems.length :=
      Nat.pow_pos (by omega : 0 < B)
    have hmul :
        B ^ G.nonterminalsFinite.elems.length * 1 <
          B ^ G.nonterminalsFinite.elems.length * B := by
      exact Nat.mul_lt_mul_of_pos_left hB hpos
    simpa using hmul
  have hFrontLt :
      Word.Length (ParseTree.frontier tree) <
        B ^ (G.nonterminalsFinite.elems.length + 1) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hFront hPowLe) hPowLt
  omega

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
compare ambiguity by parse trees with ambiguity by left derivations.
-/

def ParseTree.leftDerivationTrace {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s) :
    LeftDerivationTrace G [s]
      (SententialForm.terminalWord (ParseTree.frontier tree)) := by
  cases tree with
  | leaf a =>
      exact LeftDerivationTrace.refl _
  | node A rhs hprod children =>
      exact LeftDerivationTrace.step
        (x := [Symbol.nonterminal A]) (y := rhs)
        (by exact ⟨[], [], A, rhs, trivial, hprod, rfl, by simp⟩)
        (by
          simpa [ParseTree.frontier] using
            ParseForest.leftDerivationTrace children)

def ParseForest.leftDerivationTrace {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent) :
    LeftDerivationTrace G sent
      (SententialForm.terminalWord (ParseForest.frontier forest)) := by
  cases forest with
  | nil =>
      exact LeftDerivationTrace.refl _
  | cons s restSent tree rest =>
      have hTree :=
        (ParseTree.leftDerivationTrace tree).appendRight restSent
      have hRestPrefix :
          SententialForm.allTerminals
            (SententialForm.terminalWord
              (nt := nonterminal) (ParseTree.frontier tree)) :=
        SententialForm.terminalWord_allTerminals _
      have hRest :=
        (ParseForest.leftDerivationTrace rest).appendLeftTerminals hRestPrefix
      have hAll := hTree.trans hRest
      change LeftDerivationTrace G (s :: restSent)
        (SententialForm.terminalWord
          (Word.Concat (ParseTree.frontier tree)
            (ParseForest.frontier rest)))
      rw [SententialForm.terminalWord_append]
      exact hAll

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

The final section records left-derivation traces and proves that ambiguity by
parse trees is equivalent to ambiguity by left derivations.
-/

structure StartLeftDerivation (G : CFG terminal nonterminal)
    (w : Word terminal) where
  tree : ParseTree G (Symbol.nonterminal G.start)
  trace :
    LeftDerivationTrace G [Symbol.nonterminal G.start]
      (SententialForm.terminalWord w)
  frontier_eq : ParseTree.frontier tree = w

def StartLeftDerivation.ofParseTree {G : CFG terminal nonterminal}
    {w : Word terminal}
    (tree : ParseTree G (Symbol.nonterminal G.start))
    (hfrontier : ParseTree.frontier tree = w) :
    StartLeftDerivation G w where
  tree := tree
  trace := by
    rw [← hfrontier]
    exact ParseTree.leftDerivationTrace tree
  frontier_eq := hfrontier

def AmbiguousByLeftDerivations (G : CFG terminal nonterminal) : Prop :=
  exists w, exists d1 : StartLeftDerivation G w,
    exists d2 : StartLeftDerivation G w, d1.tree ≠ d2.tree

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
    cases h with
    | intro w hw =>
        cases hw with
        | intro t1 ht1 =>
            cases ht1 with
            | intro t2 ht2 =>
                exists w
                exists StartLeftDerivation.ofParseTree t1 ht2.left
                exists StartLeftDerivation.ofParseTree t2 ht2.right.left
                exact ht2.right.right
  · intro h
    cases h with
    | intro w hw =>
        cases hw with
        | intro d1 hd1 =>
            cases hd1 with
            | intro d2 hne =>
                exists w
                exists d1.tree
                exists d2.tree
                constructor
                · exact d1.frontier_eq
                constructor
                · exact d2.frontier_eq
                · exact hne

end CFG

end Grammars
end FoC

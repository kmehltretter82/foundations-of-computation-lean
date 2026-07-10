import FoC.Grammars.ParseTree.Paths

set_option doc.verso true

namespace FoC
namespace Grammars

open Languages

namespace CFG

/-!
# Parse-Tree Pumping Infrastructure

Selected-subtree containment, replacement, minimality, nonempty loop derivations, and frontier bounds provide the structural core of the context-free pumping argument.
-/

/-!
Given two selected subtrees on the same longest path, the lower one is inside
the upper one. If their roots match, replacing the lower subtree by a
nonterminal hole gives the loop derivation used by context-free pumping proofs.
-/

theorem ParseTree.later_selected_subtree_in_selected_subtree
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i j : Nat} {upper lower : NonterminalSubtree G}
    (hij : i <= j)
    (hupper : (ParseTree.longestNonterminalSubtrees tree)[i]? = some upper)
    (hlower : (ParseTree.longestNonterminalSubtrees tree)[j]? = some lower) :
    (ParseTree.longestNonterminalSubtrees upper.2)[j - i]? = some lower := by
  have hsuffix :=
    ParseTree.longestNonterminalSubtrees_suffix_at_index tree hupper
  have hdrop :
      (List.drop i (ParseTree.longestNonterminalSubtrees tree))[j - i]? =
        some lower := by
    rw [List.getElem?_drop]
    have hsum : i + (j - i) = j := by lia
    rw [hsum]
    exact hlower
  rw [hsuffix] at hdrop
  exact hdrop

theorem ParseTree.loop_derivation_from_repeated_selected_subtrees
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i j : Nat} {upper lower : NonterminalSubtree G}
    (hij : i <= j)
    (hupper : (ParseTree.longestNonterminalSubtrees tree)[i]? = some upper)
    (hlower : (ParseTree.longestNonterminalSubtrees tree)[j]? = some lower)
    (hroot : NonterminalSubtree.root upper = NonterminalSubtree.root lower) :
    exists x z : Word terminal,
      NonterminalSubtree.frontier upper =
        Word.Concat x (Word.Concat (NonterminalSubtree.frontier lower) z) ∧
      Derives G [Symbol.nonterminal (NonterminalSubtree.root upper)]
        (SententialForm.terminalWord x ++
          [Symbol.nonterminal (NonterminalSubtree.root upper)] ++
          SententialForm.terminalWord z) := by
  have hinside :=
    ParseTree.later_selected_subtree_in_selected_subtree
      tree hij hupper hlower
  cases ParseTree.derives_with_selected_subtree_hole upper.2 hinside with
  | intro x hx =>
      cases hx with
      | intro z hz =>
          exists x
          exists z
          constructor
          · exact hz.left
          · have hder := hz.right
            rw [← hroot] at hder
            exact hder

mutual

/-
The selected subtree is genuinely a subtree of the original parse tree, so its
node count is bounded by the whole tree. The strict version later gives the
minimality contradiction used in pumping-style replacement arguments.
-/

theorem ParseTree.selected_subtree_nodeCount_le
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    NonterminalSubtree.nodeCount subtree <= ParseTree.nodeCount tree := by
  cases tree with
  | leaf a =>
      cases hget
  | node A rhs hprod children =>
      cases i with
      | zero =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases hget
          simp [NonterminalSubtree.nodeCount]
      | succ i =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          have hle :=
            ParseForest.selected_subtree_nodeCount_le children hget
          simp [ParseTree.nodeCount]
          lia

theorem ParseForest.selected_subtree_nodeCount_le
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseForest.longestNonterminalSubtrees forest)[i]? = some subtree) :
    NonterminalSubtree.nodeCount subtree <= ParseForest.nodeCount forest := by
  cases forest with
  | nil =>
      cases hget
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        have hle :=
          ParseForest.selected_subtree_nodeCount_le rest hget
        simp [ParseForest.nodeCount]
        lia
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        have hle :=
          ParseTree.selected_subtree_nodeCount_le tree hget
        simp [ParseForest.nodeCount]
        lia

end

theorem ParseTree.selected_subtree_nodeCount_lt_of_pos_index
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hpos : 0 < i)
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    NonterminalSubtree.nodeCount subtree < ParseTree.nodeCount tree := by
  cases tree with
  | leaf a =>
      cases hget
  | node A rhs hprod children =>
      cases i with
      | zero =>
          lia
      | succ i =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          have hle :=
            ParseForest.selected_subtree_nodeCount_le children hget
          simp [ParseTree.nodeCount]
          lia

mutual

/-
Replacement reconstructs a parse tree after swapping the selected subtree with
another tree rooted at the same nonterminal. This is the tree-level operation
behind the derivation loop used by the context-free pumping argument.
-/

theorem ParseTree.exists_replace_selected_subtree
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree)
    (replacement :
      ParseTree G (Symbol.nonterminal (NonterminalSubtree.root subtree)))
    (hfront :
      ParseTree.frontier replacement = NonterminalSubtree.frontier subtree) :
    exists newTree : ParseTree G s,
      ParseTree.frontier newTree = ParseTree.frontier tree ∧
      ParseTree.nodeCount newTree + NonterminalSubtree.nodeCount subtree =
        ParseTree.nodeCount tree + ParseTree.nodeCount replacement := by
  cases tree with
  | leaf a =>
      cases hget
  | node A rhs hprod children =>
      cases i with
      | zero =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases hget
          exists replacement
          constructor
          · exact hfront
          · simp [NonterminalSubtree.nodeCount]
            rw [Nat.add_comm]
            rfl
      | succ i =>
          simp [ParseTree.longestNonterminalSubtrees] at hget
          cases ParseForest.exists_replace_selected_subtree
              children hget replacement hfront with
          | intro newChildren hnewChildren =>
              exists ParseTree.node A rhs hprod newChildren
              constructor
              · exact hnewChildren.left
              · simp [ParseTree.nodeCount]
                lia

theorem ParseForest.exists_replace_selected_subtree
    {G : CFG terminal nonterminal}
    {sent : SententialForm terminal nonterminal} (forest : ParseForest G sent)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseForest.longestNonterminalSubtrees forest)[i]? = some subtree)
    (replacement :
      ParseTree G (Symbol.nonterminal (NonterminalSubtree.root subtree)))
    (hfront :
      ParseTree.frontier replacement = NonterminalSubtree.frontier subtree) :
    exists newForest : ParseForest G sent,
      ParseForest.frontier newForest = ParseForest.frontier forest ∧
      ParseForest.nodeCount newForest + NonterminalSubtree.nodeCount subtree =
        ParseForest.nodeCount forest + ParseTree.nodeCount replacement := by
  cases forest with
  | nil =>
      cases hget
  | cons s restSent tree rest =>
      by_cases hlt : ParseTree.height tree < ParseForest.height rest
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        cases ParseForest.exists_replace_selected_subtree
            rest hget replacement hfront with
        | intro newRest hnewRest =>
            exists ParseForest.cons s restSent tree newRest
            constructor
            · simp [ParseForest.frontier, hnewRest.left, Word.Concat]
            · simp [ParseForest.nodeCount]
              lia
      · simp [ParseForest.longestNonterminalSubtrees, hlt] at hget
        cases ParseTree.exists_replace_selected_subtree
            tree hget replacement hfront with
        | intro newTree hnewTree =>
            exists ParseForest.cons s restSent newTree rest
            constructor
            · simp [ParseForest.frontier, hnewTree.left, Word.Concat]
            · simp [ParseForest.nodeCount]
              lia

end

/-
Minimality transfers to selected subtrees when the replacement would preserve the
same frontier. This lets later proofs reason locally about a repeated subtree
without violating the global minimal-tree assumption.
-/

theorem ParseTree.selected_subtree_minimal_for_frontier
    {G : CFG terminal nonterminal}
    {s : Symbol terminal nonterminal} (tree : ParseTree G s)
    (hminimal : ParseTree.MinimalForFrontier tree)
    {i : Nat} {subtree : NonterminalSubtree G}
    (hget : (ParseTree.longestNonterminalSubtrees tree)[i]? = some subtree) :
    ParseTree.MinimalForFrontier subtree.2 := by
  intro other hfront
  by_cases hle : ParseTree.nodeCount subtree.2 <= ParseTree.nodeCount other
  · exact hle
  · have hlt : ParseTree.nodeCount other < ParseTree.nodeCount subtree.2 := by
      lia
    cases ParseTree.exists_replace_selected_subtree
        tree hget other hfront with
    | intro newTree hnewTree =>
        have hnewLt : ParseTree.nodeCount newTree < ParseTree.nodeCount tree := by
          have hcountEq := hnewTree.right
          simp [NonterminalSubtree.nodeCount] at hcountEq
          have haddLt :
              ParseTree.nodeCount newTree + ParseTree.nodeCount other <
                ParseTree.nodeCount tree + ParseTree.nodeCount other := by
            calc
              ParseTree.nodeCount newTree + ParseTree.nodeCount other <
                  ParseTree.nodeCount newTree + ParseTree.nodeCount subtree.2 := by
                exact Nat.add_lt_add_left hlt _
              _ = ParseTree.nodeCount tree + ParseTree.nodeCount other := hcountEq
          exact Nat.lt_of_add_lt_add_right haddLt
        have hminLe := hminimal newTree hnewTree.left
        lia

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

end CFG
end Grammars
end FoC


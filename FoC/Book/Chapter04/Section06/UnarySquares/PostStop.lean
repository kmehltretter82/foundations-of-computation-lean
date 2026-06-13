import FoC.Book.Chapter04.Section06.UnarySquares.Potential

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

open Languages
open Grammars

def squarePostStopForm
    (emitted : Nat) (middle : SententialForm SquareTerminal SquareNT) :
    SententialForm SquareTerminal SquareNT :=
  squareTerminalAForm emitted ++ [squareN SquareNT.d] ++ middle ++
    [squareN SquareNT.e]

def SquarePostStopState (n : Nat)
    (sf : SententialForm SquareTerminal SquareNT) : Prop :=
  exists emitted middle,
    sf = squarePostStopForm emitted middle ∧
      SquareMiddleClean middle ∧
        emitted + squareMiddlePotential middle = n * n

def SquarePostStopLocalState (n emitted : Nat)
    (middle : SententialForm SquareTerminal SquareNT) : Prop :=
  SquareMiddleClean middle ∧
    emitted + squareMiddlePotential middle = n * n

/-!
**Local square invariant.** The existential state above is convenient for
derivation statements, while {name}`SquarePostStopLocalState` is the exact
payload needed after a list split has located a rewrite inside the middle
segment. The lemmas below show that each post-stop rule preserves that local
payload, or in the terminal case produces a square word.
-/

theorem squarePostStopState_of_local
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted middle) :
    SquarePostStopState n (squarePostStopForm emitted middle) := by
  exact ⟨emitted, middle, rfl, hlocal.left, hlocal.right⟩

theorem squarePostStopLocal_initial (n : Nat) :
    SquarePostStopLocalState n 0
      (squareBForm n ++ squareMarkerAForm n) := by
  constructor
  · exact squareMiddleClean_append (squareBForm_clean n)
      (squareMarkerAForm_clean n)
  · rw [squareMiddlePotential_initial_stopped]
    omega

theorem squarePostStop_initial (n : Nat) :
    SquarePostStopState n
      ([squareN SquareNT.d] ++ squareBForm n ++
        squareMarkerAForm n ++ [squareN SquareNT.e]) := by
  exists 0
  exists squareBForm n ++ squareMarkerAForm n
  constructor
  · simp [squarePostStopForm, squareTerminalAForm,
      SententialForm.terminalWord, Word.RepeatSymbol, List.append_assoc]
  constructor
  · exact squareMiddleClean_append (squareBForm_clean n)
      (squareMarkerAForm_clean n)
  · rw [squareMiddlePotential_initial_stopped]
    omega

theorem squareGrowForm_stop_post_state
    {u v : SententialForm SquareTerminal SquareNT} (n : Nat)
    (h : squareGrowForm n = u ++ [squareN SquareNT.t] ++ v) :
    SquarePostStopState n (u ++ v) := by
  have hocc := squareGrowForm_t_occurrence n h
  rw [hocc.left, hocc.right]
  simpa [List.append_assoc] using squarePostStop_initial n

theorem squareMiddleClean_moveBA
    (left right : SententialForm SquareTerminal SquareNT)
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right) :
    SquareMiddleClean
      (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
        squareN SquareNT.b] ++ right) := by
  have hlocal :
      SquareMiddleClean
        ([squareN SquareNT.markA, squareT SquareTerminal.a,
          squareN SquareNT.b] ++ right) := by
    apply squareMiddleClean_append
    · exact squareMiddleClean_append squareMiddleClean_single_markA
        (squareMiddleClean_append squareMiddleClean_single_terminal_a
          squareMiddleClean_single_b)
    · exact hright
  simpa [List.append_assoc] using
    squareMiddleClean_append hleft hlocal

theorem squareMiddleClean_moveBa
    (left right : SententialForm SquareTerminal SquareNT)
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right) :
    SquareMiddleClean
      (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
  have hlocal :
      SquareMiddleClean
        ([squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
    apply squareMiddleClean_append
    · exact squareMiddleClean_append squareMiddleClean_single_terminal_a
        squareMiddleClean_single_b
    · exact hright
  simpa [List.append_assoc] using
    squareMiddleClean_append hleft hlocal

theorem squareMiddleClean_trailing_b_iff
    (middle : SententialForm SquareTerminal SquareNT) :
    SquareMiddleClean (middle ++ [squareN SquareNT.b]) <->
      SquareMiddleClean middle := by
  constructor
  · induction middle with
    | nil =>
        intro _
        trivial
    | cons head tail ih =>
        intro h
        cases head with
        | terminal tok =>
            cases tok
            exact ih h
        | nonterminal A =>
            cases A <;> try cases h
            · exact ih h
            · exact ih h
  · intro h
    exact squareMiddleClean_append h squareMiddleClean_single_b

theorem squareMiddle_pair_split_before_E_markA
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : middle ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ v) :
    exists left right,
      middle = left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right ∧
        u = left ∧ v = right ++ [squareN SquareNT.e] := by
  induction middle generalizing u with
  | nil =>
      cases u <;> simp [squareN, ggNonterminal] at h
  | cons head tail ih =>
      cases u with
      | nil =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left
          subst head
          cases tail with
          | nil =>
              simp [squareN, ggNonterminal] at h
          | cons tailHead tailRest =>
              simp at h
              have htailHead : tailHead = squareN SquareNT.markA := h.left
              subst tailHead
              exists []
              exists tailRest
              simp [h.right]
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have htailClean : SquareMiddleClean tail := by
            cases head with
            | terminal tok =>
                cases tok
                exact hclean
            | nonterminal A =>
                cases A <;> try cases hclean
                · exact hclean
                · exact hclean
          have htail :
              tail ++ [squareN SquareNT.e] =
                urest ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ v := by
            simpa using h.right
          rcases ih htailClean htail with ⟨left, right, hmid, hu, hv⟩
          exists head :: left
          exists right
          constructor
          · simp [hmid, List.append_assoc]
          constructor
          · simp [hu]
          · exact hv

theorem squareMiddle_pair_split_before_E_terminal_a
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : middle ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ v) :
    exists left right,
      middle = left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right ∧
        u = left ∧ v = right ++ [squareN SquareNT.e] := by
  induction middle generalizing u with
  | nil =>
      cases u <;> simp [squareN, squareT, ggNonterminal, ggTerminal] at h
  | cons head tail ih =>
      cases u with
      | nil =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left
          subst head
          cases tail with
          | nil =>
              simp [squareN, squareT, ggNonterminal, ggTerminal] at h
          | cons tailHead tailRest =>
              simp at h
              have htailHead : tailHead = squareT SquareTerminal.a := h.left
              subst tailHead
              exists []
              exists tailRest
              simp [h.right]
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have htailClean : SquareMiddleClean tail := by
            cases head with
            | terminal tok =>
                cases tok
                exact hclean
            | nonterminal A =>
                cases A <;> try cases hclean
                · exact hclean
                · exact hclean
          have htail :
              tail ++ [squareN SquareNT.e] =
                urest ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ v := by
            simpa using h.right
          rcases ih htailClean htail with ⟨left, right, hmid, hu, hv⟩
          exists head :: left
          exists right
          constructor
          · simp [hmid, List.append_assoc]
          constructor
          · simp [hu]
          · exact hv

theorem sentential_pair_after_nonterminal_delimiter
    [DecidableEq nonterminal]
    {A C : nonterminal}
    {second : Symbol terminal nonterminal}
    {pref tail u v : SententialForm terminal nonterminal}
    (hne : C ≠ A)
    (hpref : SententialCountNonterminal A pref = 0)
    (h : pref ++ [ggNonterminal C] ++ tail =
      u ++ [ggNonterminal A, second] ++ v) :
    exists rest,
      u = pref ++ [ggNonterminal C] ++ rest ∧
        tail = rest ++ [ggNonterminal A, second] ++ v := by
  induction pref generalizing u with
  | nil =>
      simp at h
      cases u with
      | nil =>
          simp [ggNonterminal] at h
          exact False.elim (hne h.left)
      | cons uhead urest =>
          simp at h
          exists urest
          constructor
          · simp [h.left]
          · simpa using h.right
  | cons head rest ih =>
      cases u with
      | nil =>
          simp at h
          cases head with
          | terminal _ =>
              simp [ggNonterminal] at h
          | nonterminal B =>
              simp [ggNonterminal] at h
              have hBA : B = A := h.left
              subst B
              simp [SententialCountNonterminal] at hpref
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have hrestCount :
              SententialCountNonterminal A rest = 0 := by
            cases head with
            | terminal _ =>
                simpa [SententialCountNonterminal] using hpref
            | nonterminal B =>
                simp [SententialCountNonterminal] at hpref
                exact hpref.right
          have htail :
              rest ++ [ggNonterminal C] ++ tail =
                urest ++ [ggNonterminal A, second] ++ v := by
            simpa using h.right
          rcases ih hrestCount htail with ⟨after, hu, htailEq⟩
          exists after
          constructor
          · simp [hu]
          · exact htailEq

theorem sentential_single_after_nonterminal_delimiter
    [DecidableEq nonterminal]
    {A C : nonterminal}
    {pref tail u : SententialForm terminal nonterminal}
    (hne : C ≠ A)
    (hpref : SententialCountNonterminal A pref = 0)
    (h : pref ++ [ggNonterminal C] ++ tail =
      u ++ [ggNonterminal A]) :
    exists rest,
      u = pref ++ [ggNonterminal C] ++ rest ∧
        tail = rest ++ [ggNonterminal A] := by
  induction pref generalizing u with
  | nil =>
      simp at h
      cases u with
      | nil =>
          simp [ggNonterminal] at h
          exact False.elim (hne h.left)
      | cons uhead urest =>
          simp at h
          exists urest
          constructor
          · simp [h.left]
          · simpa using h.right
  | cons head rest ih =>
      cases u with
      | nil =>
          simp at h
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have hrestCount :
              SententialCountNonterminal A rest = 0 := by
            cases head with
            | terminal _ =>
                simpa [SententialCountNonterminal] using hpref
            | nonterminal B =>
                simp [SententialCountNonterminal] at hpref
                exact hpref.right
          have htail :
              rest ++ [ggNonterminal C] ++ tail =
                urest ++ [ggNonterminal A] := by
            simpa using h.right
          rcases ih hrestCount htail with ⟨after, hu, htailEq⟩
          exists after
          constructor
          · simp [hu]
          · exact htailEq

theorem squareMiddle_trailing_b_split_before_E
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : middle ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, squareN SquareNT.e] ++ v) :
    exists left,
      middle = left ++ [squareN SquareNT.b] ∧ u = left ∧ v = [] := by
  induction middle generalizing u with
  | nil =>
      cases u <;> simp [squareN, ggNonterminal] at h
  | cons head tail ih =>
      cases u with
      | nil =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left
          subst head
          cases tail with
          | nil =>
              simp at h
              exists []
          | cons tailHead tailRest =>
              simp at h
              have htailHead : tailHead = squareN SquareNT.e := h.left
              subst tailHead
              simp [SquareMiddleClean, squareN, ggNonterminal] at hclean
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have htailClean : SquareMiddleClean tail := by
            cases head with
            | terminal tok =>
                cases tok
                exact hclean
            | nonterminal A =>
                cases A <;> try cases hclean
                · exact hclean
                · exact hclean
          have htail :
              tail ++ [squareN SquareNT.e] =
                urest ++ [squareN SquareNT.b, squareN SquareNT.e] ++ v := by
            simpa using h.right
          rcases ih htailClean htail with ⟨left, hmid, hu, hv⟩
          exists head :: left
          constructor
          · simp [hmid]
          constructor
          · simp [hu]
          · exact hv

theorem squareSeparatedTail_no_B_pair
    (bCount aCount : Nat)
    {second : Symbol SquareTerminal SquareNT}
    (hsecondT : squareN SquareNT.t ≠ second)
    (hsecondB : squareN SquareNT.b ≠ second)
    {u v : SententialForm SquareTerminal SquareNT}
    (h : squareBForm bCount ++ [squareN SquareNT.t] ++
        squareMarkerAForm aCount ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, second] ++ v) :
    False := by
  induction bCount generalizing u with
  | zero =>
      have hcount :
          SententialCountNonterminal SquareNT.b
            (squareBForm 0 ++ [squareN SquareNT.t] ++
              squareMarkerAForm aCount ++ [squareN SquareNT.e]) = 0 := by
        have hmarkers :
            SententialCountNonterminal SquareNT.b
              (squareMarkerAForm aCount) = 0 := by
          simpa [squareMarkerAForm] using
            (sententialCountNonterminal_repeat_nonterminal_of_ne
              (terminal := SquareTerminal) (A := SquareNT.b)
              (B := SquareNT.markA) (by intro hba; cases hba) aCount)
        simp [squareBForm, Word.RepeatSymbol,
          sententialCountNonterminal_append, hmarkers,
          SententialCountNonterminal, squareN, ggNonterminal]
      exact sentential_no_nonterminal_occurrence_absurd hcount (by
        simpa [List.append_assoc] using
          (show squareBForm 0 ++ [squareN SquareNT.t] ++
              squareMarkerAForm aCount ++ [squareN SquareNT.e] =
            u ++ [squareN SquareNT.b] ++ (second :: v) by
              simpa [List.append_assoc] using h))
  | succ bCount ih =>
      change squareN SquareNT.b ::
          (squareBForm bCount ++ [squareN SquareNT.t] ++
            squareMarkerAForm aCount ++ [squareN SquareNT.e]) =
        u ++ [squareN SquareNT.b, second] ++ v at h
      cases u with
      | nil =>
          simp at h
          have htail :
              squareBForm bCount ++ [squareN SquareNT.t] ++
                  squareMarkerAForm aCount ++ [squareN SquareNT.e] =
                second :: v := by
            simpa [List.append_assoc] using h
          cases bCount with
          | zero =>
              simp [squareBForm, Word.RepeatSymbol] at htail
              exact hsecondT htail.left
          | succ b =>
              change squareN SquareNT.b ::
                  (squareBForm b ++ [squareN SquareNT.t] ++
                    squareMarkerAForm aCount ++ [squareN SquareNT.e]) =
                second :: v at htail
              simp at htail
              exact hsecondB htail.left
      | cons head rest =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left.symm
          subst head
          exact ih (by simpa [List.append_assoc] using h.right)

theorem squarePostStop_moveBA
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right)
    (hbalance :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) =
        n * n) :
    SquarePostStopState n
      (squarePostStopForm emitted
        (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
          squareN SquareNT.b] ++ right)) := by
  exists emitted
  exists left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
    squareN SquareNT.b] ++ right
  constructor
  · rfl
  constructor
  · exact squareMiddleClean_moveBA left right hleft hright
  · rw [← squareMiddlePotential_moveBA]
    exact hbalance

theorem squarePostStopState_step_moveBA
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ v) :
    SquarePostStopState n
      (u ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
        squareN SquareNT.b] ++ v) := by
  have hafter := sentential_pair_after_nonterminal_delimiter
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.b) (C := SquareNT.d)
    (second := squareN SquareNT.markA)
    (by intro hbd; cases hbd)
    (squareTerminalAForm_count_nonterminal SquareNT.b emitted)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := v) (by
      simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases hafter with ⟨afterD, hu, htail⟩
  rcases squareMiddle_pair_split_before_E_markA hclean htail with
    ⟨left, right, hmiddle, hafterEq, hv⟩
  have hlocalClean :
      SquareMiddleClean
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) := by
    rw [← hmiddle]
    exact hclean
  have hleft : SquareMiddleClean left := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareN SquareNT.markA] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_left hclean'
  have htailClean :
      SquareMiddleClean
        ([squareN SquareNT.b, squareN SquareNT.markA] ++ right) := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareN SquareNT.markA] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_right hclean'
  have hright : SquareMiddleClean right :=
    squareMiddleClean_append_right htailClean
  have hbalance' :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_moveBA hleft hright hbalance'
  rw [hu, hafterEq, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_moveBA
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right)) :
    SquarePostStopLocalState n emitted
      (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
        squareN SquareNT.b] ++ right) := by
  constructor
  · have hclean :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareN SquareNT.markA] ++
            right)) := by
      simpa [List.append_assoc] using hlocal.left
    have hleft : SquareMiddleClean left :=
      squareMiddleClean_append_left hclean
    have htail :
        SquareMiddleClean
          ([squareN SquareNT.b, squareN SquareNT.markA] ++ right) :=
      squareMiddleClean_append_right hclean
    have hright : SquareMiddleClean right :=
      squareMiddleClean_append_right htail
    exact squareMiddleClean_moveBA left right hleft hright
  · rw [← squareMiddlePotential_moveBA]
    exact hlocal.right

theorem squarePostStop_moveBa
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right)
    (hbalance :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) =
        n * n) :
    SquarePostStopState n
      (squarePostStopForm emitted
        (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right)) := by
  exists emitted
  exists left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right
  constructor
  · rfl
  constructor
  · exact squareMiddleClean_moveBa left right hleft hright
  · rw [← squareMiddlePotential_moveBa]
    exact hbalance

theorem squarePostStopState_step_moveBa
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ v) :
    SquarePostStopState n
      (u ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ v) := by
  have hafter := sentential_pair_after_nonterminal_delimiter
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.b) (C := SquareNT.d)
    (second := squareT SquareTerminal.a)
    (by intro hbd; cases hbd)
    (squareTerminalAForm_count_nonterminal SquareNT.b emitted)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := v) (by
      simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases hafter with ⟨afterD, hu, htail⟩
  rcases squareMiddle_pair_split_before_E_terminal_a hclean htail with
    ⟨left, right, hmiddle, hafterEq, hv⟩
  have hlocalClean :
      SquareMiddleClean
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) := by
    rw [← hmiddle]
    exact hclean
  have hleft : SquareMiddleClean left := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareT SquareTerminal.a] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_left hclean'
  have htailClean :
      SquareMiddleClean
        ([squareN SquareNT.b, squareT SquareTerminal.a] ++ right) := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareT SquareTerminal.a] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_right hclean'
  have hright : SquareMiddleClean right :=
    squareMiddleClean_append_right htailClean
  have hbalance' :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_moveBa hleft hright hbalance'
  rw [hu, hafterEq, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_moveBa
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right)) :
    SquarePostStopLocalState n emitted
      (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
  constructor
  · have hclean :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareT SquareTerminal.a] ++
            right)) := by
      simpa [List.append_assoc] using hlocal.left
    have hleft : SquareMiddleClean left :=
      squareMiddleClean_append_left hclean
    have htail :
        SquareMiddleClean
          ([squareN SquareNT.b, squareT SquareTerminal.a] ++ right) :=
      squareMiddleClean_append_right hclean
    have hright : SquareMiddleClean right :=
      squareMiddleClean_append_right htail
    exact squareMiddleClean_moveBa left right hleft hright
  · rw [← squareMiddlePotential_moveBa]
    exact hlocal.right

theorem squarePostStop_removeBE
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean (middle ++ [squareN SquareNT.b]))
    (hbalance :
      emitted + squareMiddlePotential (middle ++ [squareN SquareNT.b]) =
        n * n) :
    SquarePostStopState n (squarePostStopForm emitted middle) := by
  exists emitted
  exists middle
  constructor
  · rfl
  constructor
  · exact (squareMiddleClean_trailing_b_iff middle).mp hclean
  · rw [squareMiddlePotential_trailing_b] at hbalance
    exact hbalance

theorem squarePostStopState_step_removeBE
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.b, squareN SquareNT.e] ++ v) :
    SquarePostStopState n (u ++ [squareN SquareNT.e] ++ v) := by
  have hafter := sentential_pair_after_nonterminal_delimiter
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.b) (C := SquareNT.d)
    (second := squareN SquareNT.e)
    (by intro hbd; cases hbd)
    (squareTerminalAForm_count_nonterminal SquareNT.b emitted)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := v) (by
      simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases hafter with ⟨afterD, hu, htail⟩
  rcases squareMiddle_trailing_b_split_before_E hclean htail with
    ⟨left, hmiddle, hafterEq, hv⟩
  have hlocalClean : SquareMiddleClean (left ++ [squareN SquareNT.b]) := by
    rw [← hmiddle]
    exact hclean
  have hbalance' :
      emitted + squareMiddlePotential (left ++ [squareN SquareNT.b]) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_removeBE hlocalClean hbalance'
  rw [hu, hafterEq, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_removeBE
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      (middle ++ [squareN SquareNT.b])) :
    SquarePostStopLocalState n emitted middle := by
  constructor
  · exact (squareMiddleClean_trailing_b_iff middle).mp hlocal.left
  · have hbalance := hlocal.right
    rw [squareMiddlePotential_trailing_b] at hbalance
    exact hbalance

theorem squarePostStop_removeDA
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean ([squareN SquareNT.markA] ++ middle))
    (hbalance :
      emitted + squareMiddlePotential ([squareN SquareNT.markA] ++ middle) =
        n * n) :
    SquarePostStopState n (squarePostStopForm emitted middle) := by
  exists emitted
  exists middle
  constructor
  · rfl
  constructor
  · exact hclean
  · rw [squareMiddlePotential_leading_markA] at hbalance
    exact hbalance

theorem squarePostStopState_step_removeDA
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.d, squareN SquareNT.markA] ++ v) :
    SquarePostStopState n (u ++ [squareN SquareNT.d] ++ v) := by
  have htailCount :
      SententialCountNonterminal SquareNT.d
        (middle ++ [squareN SquareNT.e]) = 0 := by
    rw [sententialCountNonterminal_append, squareMiddleClean_count_d hclean]
    simp [SententialCountNonterminal, squareN, ggNonterminal]
  have huniq := sentential_unique_nonterminal_occurrence
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.d)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := [squareN SquareNT.markA] ++ v)
    (squareTerminalAForm_count_nonterminal SquareNT.d emitted)
    htailCount
    (by simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases huniq with ⟨hu, htail⟩
  rcases squareMiddle_leading_markA_of_tail hclean htail with
    ⟨rest, hmiddle, hv⟩
  have hlocalClean : SquareMiddleClean ([squareN SquareNT.markA] ++ rest) := by
    rw [← hmiddle]
    exact hclean
  have hbalance' :
      emitted + squareMiddlePotential ([squareN SquareNT.markA] ++ rest) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_removeDA hlocalClean hbalance'
  rw [hu, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_removeDA
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      ([squareN SquareNT.markA] ++ middle)) :
    SquarePostStopLocalState n emitted middle := by
  constructor
  · exact hlocal.left
  · have hbalance := hlocal.right
    rw [squareMiddlePotential_leading_markA] at hbalance
    exact hbalance

theorem squarePostStop_moveDa
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean ([squareT SquareTerminal.a] ++ middle))
    (hbalance :
      emitted + squareMiddlePotential ([squareT SquareTerminal.a] ++ middle) =
        n * n) :
    SquarePostStopState n (squarePostStopForm (emitted + 1) middle) := by
  exists emitted + 1
  exists middle
  constructor
  · rfl
  constructor
  · exact hclean
  · rw [squareMiddlePotential_leading_terminal_a] at hbalance
    omega

theorem squareTerminalAForm_succ_eq_append (n : Nat) :
    squareTerminalAForm (n + 1) =
      squareTerminalAForm n ++ [squareT SquareTerminal.a] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change squareT SquareTerminal.a :: squareTerminalAForm (n + 1) =
        squareT SquareTerminal.a ::
          (squareTerminalAForm n ++ [squareT SquareTerminal.a])
      rw [ih]

theorem squarePostStopState_step_moveDa
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.d, squareT SquareTerminal.a] ++ v) :
    SquarePostStopState n
      (u ++ [squareT SquareTerminal.a, squareN SquareNT.d] ++ v) := by
  have htailCount :
      SententialCountNonterminal SquareNT.d
        (middle ++ [squareN SquareNT.e]) = 0 := by
    rw [sententialCountNonterminal_append, squareMiddleClean_count_d hclean]
    simp [SententialCountNonterminal, squareN, ggNonterminal]
  have huniq := sentential_unique_nonterminal_occurrence
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.d)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := [squareT SquareTerminal.a] ++ v)
    (squareTerminalAForm_count_nonterminal SquareNT.d emitted)
    htailCount
    (by simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases huniq with ⟨hu, htail⟩
  rcases squareMiddle_leading_terminal_a_of_tail hclean htail with
    ⟨rest, hmiddle, hv⟩
  have hlocalClean : SquareMiddleClean ([squareT SquareTerminal.a] ++ rest) := by
    rw [← hmiddle]
    exact hclean
  have hbalance' :
      emitted + squareMiddlePotential ([squareT SquareTerminal.a] ++ rest) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_moveDa hlocalClean hbalance'
  rw [hu, hv]
  simpa [squarePostStopForm, squareTerminalAForm_succ_eq_append,
    List.append_assoc] using hstate

theorem squarePostStopLocal_moveDa
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      ([squareT SquareTerminal.a] ++ middle)) :
    SquarePostStopLocalState n (emitted + 1) middle := by
  constructor
  · exact hlocal.left
  · have hbalance := hlocal.right
    rw [squareMiddlePotential_leading_terminal_a] at hbalance
    omega

theorem squarePostStop_finish_word
    {n emitted : Nat}
    (hbalance : emitted + squareMiddlePotential [] = n * n) :
    Word.RepeatSymbol SquareTerminal.a emitted ∈ squareLanguage := by
  simp [squareMiddlePotential, squareMiddleInversions,
    squareMiddleInversionsFrom, SententialCountTerminal] at hbalance
  have hemitted : emitted = n * n := by omega
  exists n
  simp [squareWord, hemitted]

theorem squarePostStopState_step_finish_square
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.d, squareN SquareNT.e] ++ v) :
    exists word,
      u ++ v = SententialForm.terminalWord word ∧
        word ∈ squareLanguage := by
  have htailCount :
      SententialCountNonterminal SquareNT.d
        (middle ++ [squareN SquareNT.e]) = 0 := by
    rw [sententialCountNonterminal_append, squareMiddleClean_count_d hclean]
    simp [SententialCountNonterminal, squareN, ggNonterminal]
  have huniq := sentential_unique_nonterminal_occurrence
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.d)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := [squareN SquareNT.e] ++ v)
    (squareTerminalAForm_count_nonterminal SquareNT.d emitted)
    htailCount
    (by simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases huniq with ⟨hu, htail⟩
  rcases squareMiddle_empty_of_E_tail hclean htail with ⟨hmiddle, hv⟩
  have hbalance' : emitted + squareMiddlePotential [] = n * n := by
    rw [← hmiddle]
    exact hbalance
  exists Word.RepeatSymbol SquareTerminal.a emitted
  constructor
  · rw [hu, hv]
    simp [squareTerminalAForm, SententialForm.terminalWord]
  · exact squarePostStop_finish_word hbalance'

theorem squarePostStopLocal_finish_word
    {n emitted : Nat}
    (hlocal : SquarePostStopLocalState n emitted []) :
    Word.RepeatSymbol SquareTerminal.a emitted ∈ squareLanguage :=
  squarePostStop_finish_word hlocal.right

end Section06
end Chapter04
end Book
end FoC

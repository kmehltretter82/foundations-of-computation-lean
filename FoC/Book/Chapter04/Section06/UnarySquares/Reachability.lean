import FoC.Book.Chapter04.Section06.UnarySquares.PostStop

set_option doc.verso true

/-!
# Reachability

Supporting declarations and helper lemmas for Book Chapter04 Section06 UnarySquares Reachability.
-/


namespace FoC
namespace Book
namespace Chapter04
namespace Section06

open Languages
open Grammars

inductive SquareReachableState :
    SententialForm SquareTerminal SquareNT -> Prop where
  | start :
      SquareReachableState [squareN SquareNT.start]
  | grow (n : Nat) :
      SquareReachableState (squareGrowForm n)
  | post {sf : SententialForm SquareTerminal SquareNT}
      (n : Nat) (hpost : SquarePostStopState n sf) :
      SquareReachableState sf
  | terminal {word : Word SquareTerminal}
      (hword : word ∈ squareLanguage) :
      SquareReachableState (SententialForm.terminalWord word)

 /-- {name}`squarePostStopForm_count_start` captures the core lemma for this local construction. -/
theorem squarePostStopForm_count_start
    {emitted : Nat} {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.start
      (squarePostStopForm emitted middle) = 0 := by
  simp [squarePostStopForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal,
    squareMiddleClean_count_start hclean, SententialCountNonterminal,
    squareN, ggNonterminal]

 /-- {name}`squarePostStopForm_count_t` captures the core lemma for this local construction. -/
theorem squarePostStopForm_count_t
    {emitted : Nat} {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.t
      (squarePostStopForm emitted middle) = 0 := by
  simp [squarePostStopForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal,
    squareMiddleClean_count_t hclean, SententialCountNonterminal,
    squareN, ggNonterminal]

 /-- {name}`squarePostStopState_yields_reachable` captures the core lemma for this local construction. -/
theorem squarePostStopState_yields_reachable
    {x y : SententialForm SquareTerminal SquareNT}
    {n : Nat}
    (hpost : SquarePostStopState n x)
    (hstep : GeneralGrammar.Yields SquareGrammar x y) :
    SquareReachableState y := by
  rcases hpost with ⟨emitted, middle, hx, hclean, hbalance⟩
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  rw [hx] at hxstep
  rw [hystep]
  cases hprod with
  | start =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squarePostStopForm_count_start hclean) hxstep)
  | grow =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squarePostStopForm_count_t hclean) hxstep)
  | stop =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squarePostStopForm_count_t hclean) hxstep)
  | moveBA =>
      exact SquareReachableState.post n
        (squarePostStopState_step_moveBA hclean hbalance hxstep)
  | moveBa =>
      exact SquareReachableState.post n
        (squarePostStopState_step_moveBa hclean hbalance hxstep)
  | removeBE =>
      exact SquareReachableState.post n
        (squarePostStopState_step_removeBE hclean hbalance hxstep)
  | removeDA =>
      exact SquareReachableState.post n
        (squarePostStopState_step_removeDA hclean hbalance hxstep)
  | moveDa =>
      exact SquareReachableState.post n
        (squarePostStopState_step_moveDa hclean hbalance hxstep)
  | finish =>
      rcases squarePostStopState_step_finish_square hclean hbalance hxstep with
        ⟨word, hy, hword⟩
      have hterminal : SquareReachableState (u ++ v) := by
        rw [hy]
        exact SquareReachableState.terminal hword
      simpa using hterminal

 /-- {name}`squareGrowForm_count_start` captures the core lemma for this local construction. -/
theorem squareGrowForm_count_start (n : Nat) :
    SententialCountNonterminal SquareNT.start (squareGrowForm n) = 0 := by
  have hb :
      SententialCountNonterminal SquareNT.start (squareBForm n) = 0 := by
    simpa [squareBForm] using
      (sententialCountNonterminal_repeat_nonterminal_of_ne
        (terminal := SquareTerminal) (A := SquareNT.start) (B := SquareNT.b)
        (by intro h; cases h) n)
  have ha :
      SententialCountNonterminal SquareNT.start (squareMarkerAForm n) = 0 := by
    simpa [squareMarkerAForm] using
      (sententialCountNonterminal_repeat_nonterminal_of_ne
        (terminal := SquareTerminal) (A := SquareNT.start)
        (B := SquareNT.markA) (by intro h; cases h) n)
  simp [squareGrowForm, sententialCountNonterminal_append,
    hb, ha, SententialCountNonterminal, squareN, ggNonterminal]

 /-- {name}`squareGrowForm_count_terminal_a` captures the core lemma for this local construction. -/
theorem squareGrowForm_count_terminal_a (n : Nat) :
    SententialCountTerminal SquareTerminal.a (squareGrowForm n) = 0 := by
  simp [squareGrowForm, sententialCountTerminal_append,
    squareBForm_count_terminal_a, squareMarkerAForm_count_terminal_a,
    SententialCountTerminal, squareN, ggNonterminal]

 /-- {name}`squareGrowForm_yields_reachable` captures the core lemma for this local construction. -/
theorem squareGrowForm_yields_reachable
    {y : SententialForm SquareTerminal SquareNT}
    (n : Nat)
    (hstep : GeneralGrammar.Yields SquareGrammar (squareGrowForm n) y) :
    SquareReachableState y := by
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  rw [hystep]
  cases hprod with
  | start =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squareGrowForm_count_start n) hxstep)
  | grow =>
      have hocc := squareGrowForm_t_occurrence n hxstep
      rw [hocc.left, hocc.right]
      simpa [squareGrowForm, squareBForm_succ_eq_append,
        squareMarkerAForm, Word.RepeatSymbol, List.append_assoc] using
        SquareReachableState.grow (n + 1)
  | stop =>
      exact SquareReachableState.post n
        (squareGrowForm_stop_post_state n (by simpa using hxstep))
  | moveBA =>
      have hafter := sentential_pair_after_nonterminal_delimiter
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.b) (C := SquareNT.d)
        (second := squareN SquareNT.markA)
        (by intro hbd; cases hbd)
        (by simp [SententialCountNonterminal])
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := v) (by
          simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases hafter with ⟨afterD, hu, htail⟩
      exact False.elim
        (squareSeparatedTail_no_B_pair n n
          (by intro htm; cases htm)
          (by intro hbm; cases hbm)
          htail)
  | moveBa =>
      exact False.elim
        (sentential_no_terminal_occurrence_absurd
          (squareGrowForm_count_terminal_a n) (by
            exact
              (show squareGrowForm n =
                  (u ++ [squareN SquareNT.b]) ++
                    [ggTerminal SquareTerminal.a] ++ v by
                simpa [squareT, List.append_assoc] using hxstep)))
  | removeBE =>
      have hafter := sentential_pair_after_nonterminal_delimiter
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.b) (C := SquareNT.d)
        (second := squareN SquareNT.e)
        (by intro hbd; cases hbd)
        (by simp [SententialCountNonterminal])
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := v) (by
          simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases hafter with ⟨afterD, hu, htail⟩
      exact False.elim
        (squareSeparatedTail_no_B_pair n n
          (by intro hte; cases hte)
          (by intro hbe; cases hbe)
          htail)
  | removeDA =>
      have htailCount :
          SententialCountNonterminal SquareNT.d
            (squareBForm n ++ [squareN SquareNT.t] ++
              squareMarkerAForm n ++ [squareN SquareNT.e]) = 0 := by
        simp [sententialCountNonterminal_append, squareBForm_count_d,
          squareMarkerAForm_count_d, SententialCountNonterminal,
          squareN, ggNonterminal]
      have huniq := sentential_unique_nonterminal_occurrence
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.d)
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := [squareN SquareNT.markA] ++ v)
        (by simp [SententialCountNonterminal]) htailCount
        (by simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases huniq with ⟨hu, htail⟩
      cases n with
      | zero =>
          simp [squareBForm, squareMarkerAForm, Word.RepeatSymbol,
            squareN, ggNonterminal] at htail
      | succ n =>
          change squareN SquareNT.markA :: v =
            squareN SquareNT.b ::
              (squareBForm n ++ [squareN SquareNT.t] ++
                squareMarkerAForm (n + 1) ++ [squareN SquareNT.e]) at htail
          simp [squareN, ggNonterminal] at htail
  | moveDa =>
      exact False.elim
        (sentential_no_terminal_occurrence_absurd
          (squareGrowForm_count_terminal_a n) (by
            exact
              (show squareGrowForm n =
                  (u ++ [squareN SquareNT.d]) ++
                    [ggTerminal SquareTerminal.a] ++ v by
                simpa [squareT, List.append_assoc] using hxstep)))
  | finish =>
      have htailCount :
          SententialCountNonterminal SquareNT.d
            (squareBForm n ++ [squareN SquareNT.t] ++
              squareMarkerAForm n ++ [squareN SquareNT.e]) = 0 := by
        simp [sententialCountNonterminal_append, squareBForm_count_d,
          squareMarkerAForm_count_d, SententialCountNonterminal,
          squareN, ggNonterminal]
      have huniq := sentential_unique_nonterminal_occurrence
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.d)
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := [squareN SquareNT.e] ++ v)
        (by simp [SententialCountNonterminal]) htailCount
        (by simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases huniq with ⟨hu, htail⟩
      cases n with
      | zero =>
          simp [squareBForm, squareMarkerAForm, Word.RepeatSymbol,
            squareN, ggNonterminal] at htail
      | succ n =>
          change squareN SquareNT.e :: v =
            squareN SquareNT.b ::
              (squareBForm n ++ [squareN SquareNT.t] ++
                squareMarkerAForm (n + 1) ++ [squareN SquareNT.e]) at htail
          simp [squareN, ggNonterminal] at htail

 /-- {name}`squareStart_yields_reachable` captures the core lemma for this local construction. -/
theorem squareStart_yields_reachable
    {y : SententialForm SquareTerminal SquareNT}
    (hstep : GeneralGrammar.Yields SquareGrammar [squareN SquareNT.start] y) :
    SquareReachableState y := by
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  rw [hystep]
  cases hprod with
  | start =>
      have huniq := sentential_unique_nonterminal_occurrence
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.start)
        (pref := []) (tail := []) (u := u) (v := v)
        (by simp [SententialCountNonterminal])
        (by simp [SententialCountNonterminal])
        (by simpa [squareN] using hxstep)
      rcases huniq with ⟨hu, hv⟩
      rw [hu, hv]
      simpa [squareGrowForm, squareBForm, squareMarkerAForm,
        Word.RepeatSymbol, List.append_assoc] using
        SquareReachableState.grow 0
  | grow =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.t [squareN SquareNT.start] = 0)
          (by simpa [squareN] using hxstep))
  | stop =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.t [squareN SquareNT.start] = 0)
          (by simpa [squareN] using hxstep))
  | moveBA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.b [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveBa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.b [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.b] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeBE =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.b [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeDA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.d [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveDa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.d [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.d] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | finish =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.d [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))

 /-- {name}`squareTerminalState_yields_reachable` captures the core lemma for this local construction. -/
theorem squareTerminalState_yields_reachable
    {word : Word SquareTerminal}
    (_hword : word ∈ squareLanguage)
    {y : SententialForm SquareTerminal SquareNT}
    (hstep : GeneralGrammar.Yields SquareGrammar
      (SententialForm.terminalWord word) y) :
    SquareReachableState y := by
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  cases hprod with
  | start =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.start word)
          (by simpa [squareN] using hxstep))
  | grow =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.t word)
          (by simpa [squareN] using hxstep))
  | stop =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.t word)
          (by simpa [squareN] using hxstep))
  | moveBA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.b word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveBa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.b word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.b] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeBE =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.b word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeDA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.d word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveDa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.d word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.d] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | finish =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.d word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))

 /-- {name}`squareReachableState_yields_reachable` captures the core lemma for this local construction. -/
theorem squareReachableState_yields_reachable
    {x y : SententialForm SquareTerminal SquareNT}
    (hx : SquareReachableState x)
    (hstep : GeneralGrammar.Yields SquareGrammar x y) :
    SquareReachableState y := by
  cases hx with
  | start =>
      exact squareStart_yields_reachable hstep
  | grow n =>
      exact squareGrowForm_yields_reachable n hstep
  | post n hpost =>
      exact squarePostStopState_yields_reachable hpost hstep
  | terminal hword =>
      exact squareTerminalState_yields_reachable hword hstep

 /-- {name}`squareReachableState_derives` captures the core lemma for this local construction. -/
theorem squareReachableState_derives
    {x y : SententialForm SquareTerminal SquareNT}
    (h : GeneralGrammar.Derives SquareGrammar x y)
    (hx : SquareReachableState x) :
    SquareReachableState y := by
  induction h with
  | refl _ =>
      exact hx
  | step hstep _ ih =>
      exact ih (squareReachableState_yields_reachable hx hstep)

 /-- {name}`squarePostStopForm_count_d` captures the core lemma for this local construction. -/
theorem squarePostStopForm_count_d
    {emitted : Nat} {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.d
      (squarePostStopForm emitted middle) = 1 := by
  simp [squarePostStopForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal, squareMiddleClean_count_d hclean,
    SententialCountNonterminal, squareN, ggNonterminal]

 /-- {name}`squareReachableState_terminal_square` captures the core lemma for this local construction. -/
theorem squareReachableState_terminal_square
    {word : Word SquareTerminal}
    (hstate : SquareReachableState (SententialForm.terminalWord word)) :
    word ∈ squareLanguage := by
  generalize hsf : SententialForm.terminalWord word = sf at hstate
  cases hstate with
  | start =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          square_start_form_count_start hsf.symm)
  | grow n =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareGrowForm_count_d n) hsf.symm)
  | post n hpost =>
      rcases hpost with ⟨emitted, middle, hpostForm, hclean, hbalance⟩
      have hcount :
          SententialCountNonterminal SquareNT.d sf = 1 := by
        rw [hpostForm]
        exact squarePostStopForm_count_d hclean
      exact False.elim
        (sententialCountNonterminal_terminal_absurd hcount hsf.symm)
  | terminal hword =>
      have hto :=
        congrArg
          (SententialForm.toWord?
            (term := SquareTerminal) (nt := SquareNT)) hsf
      simp [SententialForm.terminalWord_toWord] at hto
      cases hto
      exact hword

 /-- {name}`square_generated_only_language` captures the core lemma for this local construction. -/
theorem square_generated_only_language
    {word : Word SquareTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage SquareGrammar) :
    word ∈ squareLanguage := by
  have hderives :
      GeneralGrammar.Derives SquareGrammar [squareN SquareNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, SquareGrammar, squareN,
      ggNonterminal] using h
  exact squareReachableState_terminal_square
    (squareReachableState_derives hderives SquareReachableState.start)

 /-- {name}`square_generated_language_exact` provides the witness needed for existential progress. -/
theorem square_generated_language_exact :
    Language.Equal (GeneralGrammar.GeneratedLanguage SquareGrammar)
      squareLanguage := by
  intro word
  constructor
  · exact square_generated_only_language
  · exact square_language_subset_generated

 /-- {name}`squareGrammar_finite_production_squareLanguage` captures the core lemma for this local construction. -/
theorem squareGrammar_finite_production_squareLanguage :
    FiniteProductionGeneralLanguage squareLanguage := by
  exists SquareNT
  exists SquareGrammar
  constructor
  · exact squareGrammar_has_finite_productions
  · exact square_generated_language_exact

end Section06
end Chapter04
end Book
end FoC

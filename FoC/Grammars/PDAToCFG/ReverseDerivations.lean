import FoC.Grammars.PDAToCFG.ProductionSoundness

set_option doc.verso true

/-!
# PDA-to-CFG reverse derivation constructors
-/

namespace FoC
namespace Grammars

open Languages

namespace PDA

/-!
The next derivation helpers erase form-language bookkeeping. They convert
production-level evidence into derivations of concrete terminal words, which is
the shape needed by the later PDA-step simulations.
-/

theorem toCFG_derives_of_production_word
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {A : ToCFGNonterminal stack state}
    {rhs : SententialForm input (ToCFGNonterminal stack state)}
    {w : Word input}
    (hprod : ToCFGProduces M A rhs)
    (hw : w ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) rhs) :
    CFG.Derives (ToCFG M presentation) [Symbol.nonterminal A]
      (SententialForm.terminalWord w) := by
  exact CFG.derives_trans (toCFG_derives_of_production hprod)
    (CFG.formLanguage_derives hw)

theorem toCFG_start_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {q : state} {w : Word input}
    (haccept : M.accept q)
    (hbody : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty M.start q)]
      (SententialForm.terminalWord w)) :
    w ∈ CFG.GeneratedLanguage (ToCFG M presentation) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.start haccept)
  exact formLanguage_single_nonterminal_derives hbody

theorem toCFG_emptyRefl_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {q : state} :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty q q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
  simpa [SententialForm.terminalWord, Word.Empty] using
    toCFG_derives_of_production
      (M := M) (presentation := presentation)
      (ToCFGProduces.emptyRefl (q := q))

theorem toCFG_popStep_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (ToCFGNonterminal stack state)}
    {pref chainWord : Word input}
    (htransition : M.transition p a? [A] r push)
    (hchain : ToCFGChain r push q chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) chainRhs) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Concat pref chainWord)) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.popStep htransition hchain)
  exact formLanguage_append_mem
    (CFG.DerivationSymbolLanguage (ToCFG M presentation)) hpref hchainWord

theorem toCFG_emptyStep_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (ToCFGNonterminal stack state)}
    {pref chainWord emptyWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChain r push s chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) chainRhs)
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord emptyWord))) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.emptyStep htransition hchain)
  have htail : Word.Concat chainWord emptyWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (chainRhs ++
        [Symbol.nonterminal (ToCFGNonterminal.empty s q)]) := by
    exact formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      hchainWord
      (formLanguage_single_nonterminal_derives hempty)
  simpa [List.append_assoc] using
    formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) hpref htail

theorem toCFG_emptyBeforeTop_derives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {chainRhs : SententialForm input (ToCFGNonterminal stack state)}
    {pref chainWord topWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChain r push s chainRhs)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hchainWord : chainWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) chainRhs)
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord topWord))) := by
  apply toCFG_derives_of_production_word
    (M := M) (presentation := presentation)
    (ToCFGProduces.emptyBeforeTop htransition hchain)
  have htail : Word.Concat chainWord topWord ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (chainRhs ++
        [Symbol.nonterminal (ToCFGNonterminal.between s A q)]) := by
    exact formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      hchainWord
      (formLanguage_single_nonterminal_derives htop)
  simpa [List.append_assoc] using
    formLanguage_append_mem
      (CFG.DerivationSymbolLanguage (ToCFG M presentation)) hpref htail

/-!
The preceding derivation lemmas work with an explicit right-hand-side chain.
The following variants package that chain as a derivation object and split the
read and epsilon cases, matching the way PDA steps are analyzed later.
-/

theorem toCFG_popStep_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {pref chainWord : Word input}
    (htransition : M.transition p a? [A] r push)
    (hchain : ToCFGChainDerives M presentation r push q chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Concat pref chainWord)) := by
  rcases toCFGChainDerives_formLanguage hchain with
    ⟨chainRhs, hchainRhs, hchainWord⟩
  exact toCFG_popStep_derives htransition hchainRhs hpref hchainWord

theorem toCFG_emptyStep_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {a? : Option input}
    {push : Word stack}
    {pref chainWord emptyWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord emptyWord))) := by
  rcases toCFGChainDerives_formLanguage hchain with
    ⟨chainRhs, hchainRhs, hchainWord⟩
  exact toCFG_emptyStep_derives htransition hchainRhs hpref
    hchainWord hempty

theorem toCFG_emptyBeforeTop_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack} {a? : Option input}
    {push : Word stack}
    {pref chainWord topWord : Word input}
    (htransition : M.transition p a? [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hpref : pref ∈ CFG.FormLanguage
      (CFG.DerivationSymbolLanguage (ToCFG M presentation))
      (inputPrefix (nonterminal := ToCFGNonterminal stack state) a?))
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat pref (Word.Concat chainWord topWord))) := by
  rcases toCFGChainDerives_formLanguage hchain with
    ⟨chainRhs, hchainRhs, hchainWord⟩
  exact toCFG_emptyBeforeTop_derives htransition hchainRhs hpref
    hchainWord htop

theorem toCFG_popRead_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack} {a : input}
    {push : Word stack} {chainWord : Word input}
    (htransition : M.transition p (some a) [A] r push)
    (hchain : ToCFGChainDerives M presentation r push q chainWord) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a) chainWord)) := by
  exact toCFG_popStep_of_chainDerives htransition hchain
    (inputPrefix_some_mem_derivationSymbolLanguage
      (ToCFG M presentation) a)

theorem toCFG_popEpsilon_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r q : state} {A : stack}
    {push : Word stack} {chainWord : Word input}
    (htransition : M.transition p none [A] r push)
    (hchain : ToCFGChainDerives M presentation r push q chainWord) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord chainWord) := by
  simpa [Word.Concat, Word.Empty] using
    toCFG_popStep_of_chainDerives htransition hchain
      (inputPrefix_none_mem_derivationSymbolLanguage
        (ToCFG M presentation))

theorem toCFG_emptyRead_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {a : input}
    {push : Word stack}
    {chainWord emptyWord : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a)
          (Word.Concat chainWord emptyWord))) := by
  exact toCFG_emptyStep_of_chainDerives htransition hchain
    (inputPrefix_some_mem_derivationSymbolLanguage
      (ToCFG M presentation) a)
    hempty

theorem toCFG_emptyEpsilon_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state}
    {push : Word stack}
    {chainWord emptyWord : Word input}
    (htransition : M.transition p none [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (hempty : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty s q)]
      (SententialForm.terminalWord emptyWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord
        (Word.Concat chainWord emptyWord)) := by
  simpa [Word.Concat, Word.Empty] using
    toCFG_emptyStep_of_chainDerives htransition hchain
      (inputPrefix_none_mem_derivationSymbolLanguage
        (ToCFG M presentation))
      hempty

theorem toCFG_emptyBeforeTopRead_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack} {a : input}
    {push : Word stack}
    {chainWord topWord : Word input}
    (htransition : M.transition p (some a) [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat (Word.Symbol a)
          (Word.Concat chainWord topWord))) := by
  exact toCFG_emptyBeforeTop_of_chainDerives htransition hchain
    (inputPrefix_some_mem_derivationSymbolLanguage
      (ToCFG M presentation) a)
    htop

theorem toCFG_emptyBeforeTopEpsilon_of_chainDerives
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p r s q : state} {A : stack}
    {push : Word stack}
    {chainWord topWord : Word input}
    (htransition : M.transition p none [] r push)
    (hchain : ToCFGChainDerives M presentation r push s chainWord)
    (htop : CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between s A q)]
      (SententialForm.terminalWord topWord)) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord
        (Word.Concat chainWord topWord)) := by
  simpa [Word.Concat, Word.Empty] using
    toCFG_emptyBeforeTop_of_chainDerives htransition hchain
      (inputPrefix_none_mem_derivationSymbolLanguage
        (ToCFG M presentation))
      htop

/-!
Now the proof turns one concrete PDA step into the corresponding CFG
derivation. There are separate empty-stack and top-pop cases because the summary
nonterminals describe those two stack effects directly.
-/

theorem toCFG_emptyRead_of_step_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {a : input} {restInput : Word input}
    (hstep : Step M
      { state := p, unread := a :: restInput, stack := [] }
      { state := q, unread := restInput, stack := [] }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord (Word.Symbol a)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunreadSource : a :: restInput = a' :: unread := by
      exact congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have ha : a = a' := (List.cons.inj hunreadSource).1
    have hunread : restInput = unread := (List.cons.inj hunreadSource).2
    have hpop : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpush : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpush
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p (some a) [] q [] := by
      simpa [hp, hq, ha, hunread, hpopNil, hpushNil] using htransition
    have hbody :=
      toCFG_emptyRead_of_chainDerives
        (M := M) (presentation := presentation)
        (p := p) (r := q) (s := q) (q := q)
        (a := a) (push := ([] : Word stack))
        (chainWord := (Word.Empty : Word input))
        (emptyWord := (Word.Empty : Word input))
        htransition'
        (ToCFGChainDerives.nil (M := M) (presentation := presentation) q)
        (toCFG_emptyRefl_derives
          (M := M) (presentation := presentation) (q := q))
    simpa [Word.Concat, Word.Empty] using hbody
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : a :: restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: restInput = restInput := by
      exact hunreadSource.trans hunreadTarget.symm
    have hlen := congrArg List.length hbad
    simp at hlen

theorem toCFG_emptyEpsilon_of_step_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {restInput : Word input}
    (hstep : Step M
      { state := p, unread := restInput, stack := [] }
      { state := q, unread := restInput, stack := [] }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : restInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: unread = unread := by
      exact hunreadSource.symm.trans hunreadTarget
    have hlen := congrArg List.length hbad
    simp at hlen
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunread : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hpop : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have hpush : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpop
      simp [Word.Concat] at hlen
      omega
    have hpushNil : push = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hpush
      simp [Word.Concat, hrestNil] at hlen
      omega
    have htransition' : M.transition p none [] q [] := by
      simpa [hp, hq, hunread, hpopNil, hpushNil] using htransition
    have hbody :=
      toCFG_emptyEpsilon_of_chainDerives
        (M := M) (presentation := presentation)
        (p := p) (r := q) (s := q) (q := q)
        (push := ([] : Word stack))
        (chainWord := (Word.Empty : Word input))
        (emptyWord := (Word.Empty : Word input))
        htransition'
        (ToCFGChainDerives.nil (M := M) (presentation := presentation) q)
        (toCFG_emptyRefl_derives
          (M := M) (presentation := presentation) (q := q))
    simpa [Word.Concat, Word.Empty] using hbody

/-!
The top-pop step cases are the stack-sensitive analogue of the empty-stack
cases. The PDA step consumes a top symbol, the chain derivation handles whatever
the transition pushes, and the generated word records the input consumed by the
step plus the input consumed while discharging the pushed stack.
-/

theorem toCFG_betweenRead_of_step_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack} {a : input}
    {restInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := a :: restInput, stack := A :: tail }
      { state := q, unread := restInput, stack := tail }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Symbol a)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunreadSource : a :: restInput = a' :: unread := by
      exact congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have ha : a = a' := (List.cons.inj hunreadSource).1
    have hunread : restInput = unread := (List.cons.inj hunreadSource).2
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' (some a') pop q' push htransition with
      hpopEmpty | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopEmpty] at hsourceLen htargetLen
      omega
    · rcases hpopSingle with ⟨B, hpopSingle⟩
      have hsourceCons : A :: tail = B :: restStack := by
        simpa [Word.Concat, hpopSingle] using hsourceStack
      have hA : A = B := (List.cons.inj hsourceCons).1
      have hrest : tail = restStack := (List.cons.inj hsourceCons).2
      have hpushNil : push = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hrestLen := congrArg List.length hrest
        have hlen := congrArg List.length htargetStack
        simp [Word.Concat] at hrestLen hlen
        omega
      have htransition' : M.transition p (some a) [A] q [] := by
        simpa [hp, hq, ha, hunread, hpopSingle, hA, hpushNil] using
          htransition
      have hbody :=
        toCFG_popRead_of_chainDerives
          (M := M) (presentation := presentation)
          (p := p) (r := q) (q := q)
          (A := A) (a := a) (push := ([] : Word stack))
          (chainWord := (Word.Empty : Word input))
          htransition'
          (ToCFGChainDerives.nil (M := M)
            (presentation := presentation) q)
      simpa [Word.Concat, Word.Empty] using hbody
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : a :: restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: restInput = restInput := by
      exact hunreadSource.trans hunreadTarget.symm
    have hlen := congrArg List.length hbad
    simp at hlen

theorem toCFG_betweenEpsilon_of_step_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack}
    {restInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := restInput, stack := A :: tail }
      { state := q, unread := restInput, stack := tail }) :
    CFG.Derives (ToCFG M presentation)
      [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
      (SententialForm.terminalWord (Word.Empty : Word input)) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    have hunreadSource : restInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hunreadTarget : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hbad : a :: unread = unread := by
      exact hunreadSource.symm.trans hunreadTarget
    have hlen := congrArg List.length hbad
    simp at hlen
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hunread : restInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hsourceStack : A :: tail = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hq : q = q' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hd
    have htargetStack : tail = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    rcases hnorm p' none pop q' push htransition with
      hpopEmpty | hpopSingle
    · have hsourceLen := congrArg List.length hsourceStack
      have htargetLen := congrArg List.length htargetStack
      simp [Word.Concat, hpopEmpty] at hsourceLen htargetLen
      omega
    · rcases hpopSingle with ⟨B, hpopSingle⟩
      have hsourceCons : A :: tail = B :: restStack := by
        simpa [Word.Concat, hpopSingle] using hsourceStack
      have hA : A = B := (List.cons.inj hsourceCons).1
      have hrest : tail = restStack := (List.cons.inj hsourceCons).2
      have hpushNil : push = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hrestLen := congrArg List.length hrest
        have hlen := congrArg List.length htargetStack
        simp [Word.Concat] at hrestLen hlen
        omega
      have htransition' : M.transition p none [A] q [] := by
        simpa [hp, hq, hunread, hpopSingle, hA, hpushNil] using
          htransition
      have hbody :=
        toCFG_popEpsilon_of_chainDerives
          (M := M) (presentation := presentation)
          (p := p) (r := q) (q := q)
          (A := A) (push := ([] : Word stack))
          (chainWord := (Word.Empty : Word input))
          htransition'
          (ToCFGChainDerives.nil (M := M)
            (presentation := presentation) q)
      simpa [Word.Concat, Word.Empty] using hbody

/-!
After the individual read and epsilon cases, the next lemmas package them into
case splitters. They are convenient interfaces for induction on computations:
the caller supplies a PDA step, and the lemma returns the consumed prefix plus
the matching summary derivation.
-/

theorem toCFG_emptyDerives_cases_of_step_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hstep : Step M
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    (sourceInput = targetInput ∧
      CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
        (SententialForm.terminalWord (Word.Empty : Word input))) ∨
    (exists a : input,
      sourceInput = a :: targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord (Word.Symbol a))) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    right
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = a :: targetInput := by
      simpa [htarget] using hsource
    refine ⟨a, hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := a :: targetInput, stack := [] }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hinput] using hstep
    exact toCFG_emptyRead_of_step_emptyStack
      (M := M) (presentation := presentation) hstep'
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    left
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = targetInput := hsource.trans htarget.symm
    refine ⟨hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := targetInput, stack := [] }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [hinput] using hstep
    exact toCFG_emptyEpsilon_of_step_emptyStack
      (M := M) (presentation := presentation) hstep'

theorem toCFG_betweenDerives_cases_of_step_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    (sourceInput = targetInput ∧
      CFG.Derives (ToCFG M presentation)
        [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
        (SententialForm.terminalWord (Word.Empty : Word input))) ∨
    (exists a : input,
      sourceInput = a :: targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord (Word.Symbol a))) := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        _htransition, hc, hd⟩
    right
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = a :: targetInput := by
      simpa [htarget] using hsource
    refine ⟨a, hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := a :: targetInput, stack := A :: tail }
        { state := q, unread := targetInput, stack := tail } := by
      simpa [hinput] using hstep
    exact toCFG_betweenRead_of_step_topPop
      (M := M) (presentation := presentation) hnorm hstep'
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        _htransition, hc, hd⟩
    left
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have htarget : targetInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hd
    have hinput : sourceInput = targetInput := hsource.trans htarget.symm
    refine ⟨hinput, ?_⟩
    have hstep' : Step M
        { state := p, unread := targetInput, stack := A :: tail }
        { state := q, unread := targetInput, stack := tail } := by
      simpa [hinput] using hstep
    exact toCFG_betweenEpsilon_of_step_topPop
      (M := M) (presentation := presentation) hnorm hstep'

/-!
For short computations, the proof can reason by explicit step count. These
bounded lemmas are the base cases for the later summary-computation induction:
zero, one, and two normalized PDA steps are converted into CFG derivations.
-/

theorem step_sourceStack_empty_or_single_of_step_to_emptyStack
    {M : PDA input stack state}
    {p q : state} {sourceInput targetInput : Word input}
    {sourceStack : Word stack}
    (hnorm : PopsAtMostOne M)
    (hstep : Step M
      { state := p, unread := sourceInput, stack := sourceStack }
      { state := q, unread := targetInput, stack := [] }) :
    sourceStack = [] ∨ exists A : stack, sourceStack = [A] := by
  rcases step_cases hstep with hread | heps
  · rcases hread with
      ⟨p', q', a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hsourceStack : sourceStack = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have htargetStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length htargetStack
      simp [Word.Concat] at hlen
      omega
    rcases hnorm p' (some a) pop q' push htransition with
      hpopNil | hpopSingle
    · left
      simpa [Word.Concat, hpopNil, hrestNil] using hsourceStack
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      right
      refine ⟨A, ?_⟩
      simpa [Word.Concat, hpopSingle, hrestNil] using hsourceStack
  · rcases heps with
      ⟨p', q', unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hsourceStack : sourceStack = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have htargetStack : ([] : Word stack) = Word.Concat push restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hd
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length htargetStack
      simp [Word.Concat] at hlen
      omega
    rcases hnorm p' none pop q' push htransition with
      hpopNil | hpopSingle
    · left
      simpa [Word.Concat, hpopNil, hrestNil] using hsourceStack
    · rcases hpopSingle with ⟨A, hpopSingle⟩
      right
      refine ⟨A, ?_⟩
      simpa [Word.Concat, hpopSingle, hrestNil] using hsourceStack

theorem toCFG_emptyDerives_of_computesIn_zero_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 0
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  have hend := computesIn_zero_eq hcomp
  have hstate : p = q := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.state) hend
  have hunread : sourceInput = targetInput := by
    simpa using congrArg
      (fun c : Configuration input stack state => c.unread) hend
  refine ⟨Word.Empty, ?_, ?_⟩
  · simpa [Word.Concat, Word.Empty] using hunread
  · simpa [hstate, SententialForm.terminalWord, Word.Empty] using
      toCFG_emptyRefl_derives
        (M := M) (presentation := presentation) (q := p)

/-!
For one-step empty-stack computations, the zero-step base case above is joined
with the step case splitter. This is the first bounded-computation theorem that
turns a concrete PDA run into a CFG derivation.
-/

theorem toCFG_emptyDerives_of_computesIn_one_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  have hstep := computesIn_one_inv hcomp
  rcases toCFG_emptyDerives_cases_of_step_emptyStack
      (M := M) (presentation := presentation) hstep with
    hempty | hread
  · rcases hempty with ⟨hinput, hderive⟩
    refine ⟨Word.Empty, ?_, ?_⟩
    · simpa [Word.Concat, Word.Empty] using hinput
    · simpa [Word.Empty] using hderive
  · rcases hread with ⟨a, hinput, hderive⟩
    refine ⟨Word.Symbol a, ?_, ?_⟩
    · simpa [Word.Concat, Word.Symbol] using hinput
    · exact hderive

theorem toCFG_emptyDerives_of_computesIn_atMostOne_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hn : n <= 1)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  cases n with
  | zero =>
      exact toCFG_emptyDerives_of_computesIn_zero_emptyStack
        (M := M) (presentation := presentation) hcomp
  | succ n =>
      cases n with
      | zero =>
          exact toCFG_emptyDerives_of_computesIn_one_emptyStack
            (M := M) (presentation := presentation) hcomp
      | succ n =>
          omega

theorem toCFG_betweenDerives_of_computesIn_one_topPop
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {A : stack}
    {sourceInput targetInput : Word input} {tail : Word stack}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 1
      { state := p, unread := sourceInput, stack := A :: tail }
      { state := q, unread := targetInput, stack := tail }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.between p A q)]
          (SententialForm.terminalWord consumed) := by
  have hstep := computesIn_one_inv hcomp
  rcases toCFG_betweenDerives_cases_of_step_topPop
      (M := M) (presentation := presentation) hnorm hstep with
    hempty | hread
  · rcases hempty with ⟨hinput, hderive⟩
    refine ⟨Word.Empty, ?_, ?_⟩
    · simpa [Word.Concat, Word.Empty] using hinput
    · simpa [Word.Empty] using hderive
  · rcases hread with ⟨a, hinput, hderive⟩
    refine ⟨Word.Symbol a, ?_, ?_⟩
    · simpa [Word.Concat, Word.Symbol] using hinput
    · exact hderive

/-!
Two-step empty-stack computations are the first place where normalization
matters. The first step may expose a temporary stack symbol; the proof handles
that by deriving a between-summary for the top symbol and then closing the
remaining empty-stack suffix.
-/

theorem toCFG_emptyDerives_of_computesIn_two_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hcomp : ComputesIn M 2
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  rcases computesIn_succ_inv (M := M) (n := 1) hcomp with
    ⟨mid, hfirst, htail⟩
  have hsecond0 : Step M mid
      { state := q, unread := targetInput, stack := [] } :=
    computesIn_one_inv htail
  rcases step_cases hfirst with hread | heps
  · rcases hread with
      ⟨p', r, a, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = a :: unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p (some a) [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p (some a) [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      rcases toCFG_emptyDerives_of_computesIn_one_emptyStack
          (M := M) (presentation := presentation)
          (computesIn_of_step hsecondEmpty) with
        ⟨restWord, hrestInput, hrestDerive⟩
      let consumed := Word.Concat (Word.Symbol a) restWord
      have hsourceConsumed :
          sourceInput = Word.Concat consumed targetInput := by
        rw [hsource, hrestInput]
        simp [consumed, Word.Concat, Word.Symbol]
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed, Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := r) (q := q)
            (a := a) (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := restWord)
            htransitionEmpty
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r)
            hrestDerive
      exact ⟨consumed, hsourceConsumed, hbody⟩
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p (some a) [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      rcases toCFG_betweenDerives_of_computesIn_one_topPop
          (M := M) (presentation := presentation) hnorm
          (computesIn_of_step hsecondTop) with
        ⟨topWord, htopInput, htopDerive⟩
      let consumed := Word.Concat (Word.Symbol a) topWord
      have hsourceConsumed :
          sourceInput = Word.Concat consumed targetInput := by
        rw [hsource, htopInput]
        simp [consumed, Word.Concat, Word.Symbol]
      have hchain : ToCFGChainDerives M presentation r [A] q topWord := by
        simpa [Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons htopDerive
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
        simpa [consumed, Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyRead_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := q) (q := q)
            (a := a) (push := [A])
            (chainWord := topWord)
            (emptyWord := (Word.Empty : Word input))
            htransitionSingle hchain
            (toCFG_emptyRefl_derives
              (M := M) (presentation := presentation) (q := q))
      exact ⟨consumed, hsourceConsumed, hbody⟩
  · rcases heps with
      ⟨p', r, unread, pop, push, restStack,
        htransition, hc, hd⟩
    have hp : p = p' := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.state) hc
    have hsource : sourceInput = unread := by
      simpa using congrArg
        (fun c : Configuration input stack state => c.unread) hc
    have hstack : ([] : Word stack) = Word.Concat pop restStack := by
      exact congrArg
        (fun c : Configuration input stack state => c.stack) hc
    have hpopNil : pop = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have hrestNil : restStack = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hstack
      simp [Word.Concat] at hlen
      omega
    have htransition' :
        M.transition p none [] r push := by
      simpa [hp, hpopNil] using htransition
    cases hd
    have hsecond : Step M
        { state := r, unread := unread, stack := push }
        { state := q, unread := targetInput, stack := [] } := by
      simpa [Word.Concat, hrestNil] using hsecond0
    rcases step_sourceStack_empty_or_single_of_step_to_emptyStack
        (M := M) hnorm hsecond with hpushNil | hpushSingle
    · have htransitionEmpty :
          M.transition p none [] r [] := by
        simpa [hpushNil] using htransition'
      have hsecondEmpty : Step M
          { state := r, unread := unread, stack := [] }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushNil] using hsecond
      rcases toCFG_emptyDerives_of_computesIn_one_emptyStack
          (M := M) (presentation := presentation)
          (computesIn_of_step hsecondEmpty) with
        ⟨restWord, hrestInput, hrestDerive⟩
      have hsourceConsumed :
          sourceInput = Word.Concat restWord targetInput := by
        rw [hsource, hrestInput]
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord restWord) := by
        simpa [Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := r) (q := q)
            (push := ([] : Word stack))
            (chainWord := (Word.Empty : Word input))
            (emptyWord := restWord)
            htransitionEmpty
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) r)
            hrestDerive
      exact ⟨restWord, hsourceConsumed, hbody⟩
    · rcases hpushSingle with ⟨A, hpushSingle⟩
      have htransitionSingle :
          M.transition p none [] r [A] := by
        simpa [hpushSingle] using htransition'
      have hsecondTop : Step M
          { state := r, unread := unread, stack := A :: ([] : Word stack) }
          { state := q, unread := targetInput, stack := [] } := by
        simpa [hpushSingle] using hsecond
      rcases toCFG_betweenDerives_of_computesIn_one_topPop
          (M := M) (presentation := presentation) hnorm
          (computesIn_of_step hsecondTop) with
        ⟨topWord, htopInput, htopDerive⟩
      have hsourceConsumed :
          sourceInput = Word.Concat topWord targetInput := by
        rw [hsource, htopInput]
      have hchain : ToCFGChainDerives M presentation r [A] q topWord := by
        simpa [Word.Concat, Word.Empty] using
          ToCFGChainDerives.cons htopDerive
            (ToCFGChainDerives.nil (M := M)
              (presentation := presentation) q)
      have hbody : CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord topWord) := by
        simpa [Word.Concat, Word.Empty, List.append_assoc] using
          toCFG_emptyEpsilon_of_chainDerives
            (M := M) (presentation := presentation)
            (p := p) (r := r) (s := q) (q := q)
            (push := [A])
            (chainWord := topWord)
            (emptyWord := (Word.Empty : Word input))
            htransitionSingle hchain
            (toCFG_emptyRefl_derives
              (M := M) (presentation := presentation) (q := q))
      exact ⟨topWord, hsourceConsumed, hbody⟩

/-!
The at-most-two wrapper keeps the small-computation interface uniform. It
dispatches to the zero-, one-, or two-step theorem and hides the arithmetic case
split from downstream conversion lemmas.
-/

theorem toCFG_emptyDerives_of_computesIn_atMostTwo_emptyStack
    {M : PDA input stack state} {presentation : FinitePresentation M}
    {n : Nat} {p q : state} {sourceInput targetInput : Word input}
    (hnorm : PopsAtMostOne M)
    (hn : n <= 2)
    (hcomp : ComputesIn M n
      { state := p, unread := sourceInput, stack := [] }
      { state := q, unread := targetInput, stack := [] }) :
    exists consumed : Word input,
      sourceInput = Word.Concat consumed targetInput ∧
        CFG.Derives (ToCFG M presentation)
          [Symbol.nonterminal (ToCFGNonterminal.empty p q)]
          (SententialForm.terminalWord consumed) := by
  cases n with
  | zero =>
      exact toCFG_emptyDerives_of_computesIn_zero_emptyStack
        (M := M) (presentation := presentation) hcomp
  | succ n =>
      cases n with
      | zero =>
          exact toCFG_emptyDerives_of_computesIn_one_emptyStack
            (M := M) (presentation := presentation) hcomp
      | succ n =>
          cases n with
          | zero =>
              exact toCFG_emptyDerives_of_computesIn_two_emptyStack
                (M := M) (presentation := presentation) hnorm hcomp
          | succ n =>
              omega

/-!
The summary-computation predicates are custom induction principles for the
conversion proof. Instead of inducting over arbitrary PDA computations, they
classify runs by the stack effect that the matching CFG nonterminal is meant to
summarize.
-/


end PDA

end Grammars
end FoC

import FoC.Computability.Grammar.FinitePresentation

set_option doc.verso true

/-!
# Semantic and finite trace grammars
-/

namespace FoC
namespace Computability

open Languages
open Grammars

/-!
# Semantic unrestricted grammars

The formal {name}`GeneralGrammar.Generated` predicate allows an arbitrary
production relation. Without a finite or effective-presentation requirement,
one nonterminal and one production schema can generate any language. This is a
useful sanity check for Chapter 5: the mathematically substantive theorem is
about finite/effective grammars, while the reverse direction for unrestricted
semantic grammars is immediate.
-/

theorem generalGrammar_derivesIn_zero_eq
    {G : GeneralGrammar terminal nonterminal}
    {x z : SententialForm terminal nonterminal}
    (h : GeneralGrammar.DerivesIn G 0 x z) : z = x := by
  cases h
  rfl

theorem generalGrammar_derivesIn_succ_cases
    {G : GeneralGrammar terminal nonterminal}
    {n : Nat} {x z : SententialForm terminal nonterminal}
    (h : GeneralGrammar.DerivesIn G (n + 1) x z) :
    exists y : SententialForm terminal nonterminal,
      GeneralGrammar.Yields G x y ∧ GeneralGrammar.DerivesIn G n y z := by
  cases h with
  | step hstep hrest =>
      exact ⟨_, hstep, hrest⟩

def SemanticLanguageGrammar (L : Language terminal) :
    GeneralGrammar terminal Unit where
  start := ()
  produces := fun lhs rhs =>
    lhs = [Symbol.nonterminal ()] ∧
      exists w : Word terminal, w ∈ L ∧
        rhs = SententialForm.terminalWord w
  lhsContainsNonterminal := by
    intro lhs rhs h
    rw [h.left]
    exact SententialForm.containsNonterminal_singleton ()
  nonterminalsFinite := Grammars.FiniteType.unit

theorem semanticLanguageGrammar_nonterminal_not_mem_terminalWord
    (w : Word terminal) :
    Symbol.nonterminal () ∉
      (SententialForm.terminalWord (nt := Unit) w) := by
  induction w with
  | nil => simp [SententialForm.terminalWord]
  | cons _ _ _ => simp [SententialForm.terminalWord]

theorem semanticLanguageGrammar_start_not_terminalWord
    (w : Word terminal) :
    ([Symbol.nonterminal ()] : SententialForm terminal Unit) ≠
      SententialForm.terminalWord w := by
  intro h
  have hmem : Symbol.nonterminal () ∈
      (SententialForm.terminalWord (nt := Unit) w) := by
    rw [← h]
    simp
  exact semanticLanguageGrammar_nonterminal_not_mem_terminalWord w hmem

theorem semanticLanguageGrammar_yields_from_start
    {L : Language terminal} {y : SententialForm terminal Unit}
    (h : GeneralGrammar.Yields (SemanticLanguageGrammar L)
      [Symbol.nonterminal ()] y) :
    exists w : Word terminal, w ∈ L ∧
      y = SententialForm.terminalWord w := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨hlhs, w, hw, hrhs⟩
  have hx' : ([Symbol.nonterminal ()] : SententialForm terminal Unit) =
      u ++ [Symbol.nonterminal ()] ++ v := by
    simpa [hlhs] using hx
  have hlen := congrArg List.length hx'
  simp at hlen
  have huLen : u.length = 0 := by omega
  have hvLen : v.length = 0 := by omega
  have hu : u = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact huLen
  have hv : v = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact hvLen
  exists w
  constructor
  · exact hw
  · simpa [hu, hv, hrhs] using hy

theorem semanticLanguageGrammar_no_yields_from_terminalWord
    {L : Language terminal} (w : Word terminal)
    {y : SententialForm terminal Unit} :
    ¬ GeneralGrammar.Yields (SemanticLanguageGrammar L)
      (SententialForm.terminalWord w) y := by
  intro h
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, _⟩
  rcases hprod with ⟨hlhs, _w, _hw, _hrhs⟩
  have hmem : Symbol.nonterminal () ∈
      (SententialForm.terminalWord (nt := Unit) w) := by
    rw [hx, hlhs]
    simp
  exact semanticLanguageGrammar_nonterminal_not_mem_terminalWord w hmem

theorem semanticLanguageGrammar_derivesIn_from_terminalWord_eq
    {L : Language terminal} (w : Word terminal)
    {n : Nat} {x z : SententialForm terminal Unit}
    (h : GeneralGrammar.DerivesIn (SemanticLanguageGrammar L) n x z)
    (hx : x = SententialForm.terminalWord w) :
    z = SententialForm.terminalWord w := by
  induction h with
  | zero _ =>
      exact hx
  | step hstep _ _ =>
      have hstep' := hstep
      rw [hx] at hstep'
      exact False.elim
        (semanticLanguageGrammar_no_yields_from_terminalWord w hstep')

theorem semanticLanguageGrammar_generates
    (L : Language terminal) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage (SemanticLanguageGrammar L)) L := by
  intro w
  constructor
  · intro h
    rcases GeneralGrammar.derives_derivesIn h with ⟨n, hn⟩
    cases n with
    | zero =>
        have hforms := generalGrammar_derivesIn_zero_eq hn
        exact False.elim
          (semanticLanguageGrammar_start_not_terminalWord w hforms.symm)
    | succ n =>
        rcases generalGrammar_derivesIn_succ_cases hn with
          ⟨y, hstep, hrest⟩
        rcases semanticLanguageGrammar_yields_from_start hstep with
          ⟨w₀, hw₀, hy⟩
        have hforms :=
          semanticLanguageGrammar_derivesIn_from_terminalWord_eq w₀
            hrest hy
        have hword : w = w₀ := by
          have hto := congrArg SententialForm.toWord? hforms
          simp [SententialForm.terminalWord_toWord] at hto
          exact hto
        simpa [hword] using hw₀
  · intro hw
    exact GeneralGrammar.Derives.step
      (by
        exists ([] : SententialForm terminal Unit)
        exists ([] : SententialForm terminal Unit)
        exists ([Symbol.nonterminal ()] : SententialForm terminal Unit)
        exists SententialForm.terminalWord (nt := Unit) w
        constructor
        · constructor
          · rfl
          · exact ⟨w, hw, rfl⟩
        · constructor <;> simp)
      (GeneralGrammar.Derives.refl _)

theorem semanticLanguageGrammar_generated
    (L : Language terminal) :
    GeneralGrammar.Generated L := by
  exists Unit
  exists SemanticLanguageGrammar L
  exact semanticLanguageGrammar_generates L

theorem recursivelyEnumerableToGeneralGrammarPrinciple_semantic
    (terminal : Type u) :
    forall L : Language terminal,
      RecursivelyEnumerable L -> GeneralGrammar.Generated L := by
  intro L _hL
  exact semanticLanguageGrammar_generated L

def AcceptanceTraceLanguage
    (trace : Word terminal -> Nat -> Prop) : Language terminal :=
  fun w => exists n : Nat, trace w n

def TraceSimulationGrammar
    (trace : Word terminal -> Nat -> Prop) :
    GeneralGrammar terminal Unit :=
  SemanticLanguageGrammar (AcceptanceTraceLanguage trace)

theorem traceSimulationGrammar_derivesIn_one_of_trace
    {trace : Word terminal -> Nat -> Prop}
    {w : Word terminal} {n : Nat}
    (h : trace w n) :
    GeneralGrammar.DerivesIn (TraceSimulationGrammar trace) 1
      [Symbol.nonterminal ()]
      (SententialForm.terminalWord w) := by
  have hyield :
      GeneralGrammar.Yields (TraceSimulationGrammar trace)
        [Symbol.nonterminal ()]
        (SententialForm.terminalWord w) := by
    exists ([] : SententialForm terminal Unit)
    exists ([] : SententialForm terminal Unit)
    exists ([Symbol.nonterminal ()] : SententialForm terminal Unit)
    exists SententialForm.terminalWord (nt := Unit) w
    constructor
    · constructor
      · rfl
      · exact ⟨w, ⟨n, h⟩, rfl⟩
    · constructor <;> simp
  exact GeneralGrammar.DerivesIn.step hyield
    (GeneralGrammar.DerivesIn.zero
      (SententialForm.terminalWord w))

theorem traceSimulationGrammar_generated_of_acceptanceTrace
    {trace : Word terminal -> Nat -> Prop}
    {L : Language terminal}
    (htrace : AcceptanceTrace trace L) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (TraceSimulationGrammar trace)) L :=
  Language.equal_trans
    (semanticLanguageGrammar_generates (AcceptanceTraceLanguage trace))
    htrace

theorem acceptanceTrace_generated_by_traceSimulationGrammar
    {trace : Word terminal -> Nat -> Prop}
    {L : Language terminal}
    (htrace : AcceptanceTrace trace L) :
    GeneralGrammar.Generated L := by
  exists Unit
  exists TraceSimulationGrammar trace
  exact traceSimulationGrammar_generated_of_acceptanceTrace htrace

def MachineHaltingTraceSimulationGrammar
    (D : MachineDescription) : GeneralGrammar Bool Unit :=
  TraceSimulationGrammar (fun w n => D.HaltsIn n w)

theorem machineHaltingTraceSimulationGrammar_derivesIn_one_of_haltsIn
    {D : MachineDescription} {w : Word Bool} {n : Nat}
    (h : D.HaltsIn n w) :
    GeneralGrammar.DerivesIn
      (MachineHaltingTraceSimulationGrammar D) 1
      [Symbol.nonterminal ()]
      (SententialForm.terminalWord w) :=
  traceSimulationGrammar_derivesIn_one_of_trace h

theorem machineHaltingTraceSimulationGrammar_generated
    (D : MachineDescription) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (MachineHaltingTraceSimulationGrammar D))
      (fun w => D.HaltsOnInput w) :=
  traceSimulationGrammar_generated_of_acceptanceTrace (by
    intro w
    rfl)

theorem machineDescription_accepts_generated_by_traceSimulationGrammar
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (MachineHaltingTraceSimulationGrammar D)) L :=
  Language.equal_trans
    (machineHaltingTraceSimulationGrammar_generated D)
    h.right

/-!
# Finite trace-table grammars

The semantic trace grammar above is intentionally liberal: an arbitrary trace
predicate becomes an arbitrary production predicate.  The finite/effective
target needs a different interface.  A finite trace table is concrete data: a
finite list of accepted words with their witnessing stages.  Its grammar is the
same one-step language grammar, but now the production relation is witnessed by
an explicit finite list of start-to-word productions.
-/

structure FiniteAcceptanceTraceTable (terminal : Type u) where
  entries : List (Word terminal × Nat)

namespace FiniteAcceptanceTraceTable

def language (T : FiniteAcceptanceTraceTable terminal) :
    Language terminal :=
  fun w => exists n : Nat, (w, n) ∈ T.entries

def words (T : FiniteAcceptanceTraceTable terminal) :
    List (Word terminal) :=
  T.entries.map Prod.fst

def grammar (T : FiniteAcceptanceTraceTable terminal) :
    GeneralGrammar terminal Unit :=
  SemanticLanguageGrammar T.language

def productions (T : FiniteAcceptanceTraceTable terminal) :
    List (GeneralGrammar.Production terminal Unit) :=
  T.words.map
    (fun w =>
      { lhs := ([Symbol.nonterminal ()] : SententialForm terminal Unit)
        rhs := SententialForm.terminalWord w })

theorem mem_words_iff
    (T : FiniteAcceptanceTraceTable terminal) (w : Word terminal) :
    w ∈ T.words <-> exists n : Nat, (w, n) ∈ T.entries := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨entry, hentry, hfst⟩
    rcases entry with ⟨w₀, n⟩
    simp at hfst
    cases hfst
    exact ⟨n, hentry⟩
  · intro h
    rcases h with ⟨n, hentry⟩
    exact List.mem_map.mpr ⟨(w, n), hentry, rfl⟩

theorem productionListProduces_iff_produces
    (T : FiniteAcceptanceTraceTable terminal)
    (lhs rhs : SententialForm terminal Unit) :
    GeneralGrammar.ProductionListProduces T.productions lhs rhs <->
      (T.grammar).produces lhs rhs := by
  constructor
  · intro h
    rcases h with ⟨rule, hrule, hlhs, hrhs⟩
    rcases List.mem_map.mp hrule with ⟨w, hw, hruleEq⟩
    have hmem : w ∈ T.language :=
      (T.mem_words_iff w).mp hw
    rw [← hruleEq] at hlhs hrhs
    constructor
    · simpa [productions] using hlhs.symm
    · exact ⟨w, hmem, by simpa [productions] using hrhs.symm⟩
  · intro h
    rcases h with ⟨hlhs, w, hw, hrhs⟩
    have hwWords : w ∈ T.words :=
      (T.mem_words_iff w).mpr hw
    refine ⟨
      { lhs := ([Symbol.nonterminal ()] : SententialForm terminal Unit)
        rhs := SententialForm.terminalWord w },
      ?_, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨w, hwWords, rfl⟩
    · simp [hlhs]
    · simp [hrhs]

theorem hasFiniteProductions
    (T : FiniteAcceptanceTraceTable terminal) :
    GeneralGrammar.HasFiniteProductions T.grammar := by
  exists T.productions
  intro lhs rhs
  exact (T.productionListProduces_iff_produces lhs rhs).symm

theorem generated_language
    (T : FiniteAcceptanceTraceTable terminal) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage T.grammar) T.language :=
  semanticLanguageGrammar_generates T.language

theorem finiteProductionGenerated_language
    (T : FiniteAcceptanceTraceTable terminal) :
    GeneralGrammar.FiniteProductionGenerated T.language := by
  exists Unit
  exists T.grammar
  exact ⟨T.hasFiniteProductions, T.generated_language⟩

def PresentsLanguage
    (T : FiniteAcceptanceTraceTable terminal)
    (L : Language terminal) : Prop :=
  Language.Equal T.language L

theorem finiteProductionGenerated_of_presents
    {T : FiniteAcceptanceTraceTable terminal}
    {L : Language terminal}
    (h : T.PresentsLanguage L) :
    GeneralGrammar.FiniteProductionGenerated L := by
  rcases T.finiteProductionGenerated_language with ⟨nonterminal, G, hG⟩
  exists nonterminal
  exists G
  exact ⟨hG.left, Language.equal_trans hG.right h⟩

end FiniteAcceptanceTraceTable

def FiniteTraceTableRecognizable (L : Language terminal) : Prop :=
  exists T : FiniteAcceptanceTraceTable terminal, T.PresentsLanguage L

def FiniteTraceTableToFiniteGeneralGrammarConstruction
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FiniteTraceTableRecognizable L ->
      GeneralGrammar.FiniteProductionGenerated L

theorem finiteTraceTableRecognizable_finiteProductionGenerated
    {L : Language terminal}
    (h : FiniteTraceTableRecognizable L) :
    GeneralGrammar.FiniteProductionGenerated L := by
  rcases h with ⟨T, hT⟩
  exact T.finiteProductionGenerated_of_presents hT

theorem finiteTraceTableToFiniteGeneralGrammarConstruction
    (terminal : Type u) :
    FiniteTraceTableToFiniteGeneralGrammarConstruction terminal := by
  intro L hL
  exact finiteTraceTableRecognizable_finiteProductionGenerated hL

def MachineFiniteAcceptanceTraceTable (_D : MachineDescription) :
    Type :=
  FiniteAcceptanceTraceTable Bool

def MachineFiniteAcceptanceTraceTable.Presents
    (D : MachineDescription)
    (T : MachineFiniteAcceptanceTraceTable D) : Prop :=
  T.PresentsLanguage (fun w : Word Bool => D.HaltsOnInput w)

theorem machineFiniteAcceptanceTraceTable_generated
    {D : MachineDescription}
    {T : MachineFiniteAcceptanceTraceTable D}
    (hT : MachineFiniteAcceptanceTraceTable.Presents D T) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage T.grammar)
      (fun w : Word Bool => D.HaltsOnInput w) :=
  Language.equal_trans T.generated_language hT

theorem machineFiniteAcceptanceTraceTable_finiteProductionGenerated
    {D : MachineDescription}
    {T : MachineFiniteAcceptanceTraceTable D}
    (hT : MachineFiniteAcceptanceTraceTable.Presents D T) :
    GeneralGrammar.FiniteProductionGenerated
      (fun w : Word Bool => D.HaltsOnInput w) :=
  T.finiteProductionGenerated_of_presents hT


end Computability
end FoC

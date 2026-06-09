import FoC.Computability.Compiler
import FoC.Grammars.GeneralGrammar

set_option doc.verso true

/-!
# General grammar recognizers

## Derivations as staged recognition

Finite derivations of a general grammar are finite-stage evidence.  This file
turns the length-indexed derivation relation from
{module}`FoC.Grammars.GeneralGrammar` into an acceptance trace and a staged
program recognizer.

The construction stays at the staged-program layer.  Compiling this recognizer
to a concrete one-tape Turing machine is the later universal/interpreter
development.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: the direction from finite general grammars to
  recursively enumerable behavior.
-/

namespace FoC
namespace Computability

open Languages
open Grammars

/-!
# Grammar derivation traces
-/

def GeneralGrammarDerivationTrace
    (G : GeneralGrammar terminal nonterminal)
    (w : Word terminal) (n : Nat) : Prop :=
  GeneralGrammar.DerivesIn G n
    [Symbol.nonterminal G.start]
    (SententialForm.terminalWord w)

def FiniteProductionListDerivationTrace
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  GeneralGrammar.ProductionListDerivesIn rules n
    [Symbol.nonterminal G.start]
    (SententialForm.terminalWord w)

theorem finiteProductionListDerivationTrace_iff_derivationTrace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {n : Nat} :
    FiniteProductionListDerivationTrace G rules w n <->
      GeneralGrammarDerivationTrace G w n :=
  GeneralGrammar.productionListDerivesIn_iff_derivesIn_of_produces
    hrules

theorem generalGrammar_derivationTrace_acceptance
    (G : GeneralGrammar terminal nonterminal) :
    AcceptanceTrace
      (GeneralGrammarDerivationTrace G)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  constructor
  · intro h
    cases h with
    | intro _ hn =>
        exact GeneralGrammar.derivesIn_derives hn
  · intro h
    exact GeneralGrammar.derives_derivesIn h

theorem finiteProductionListDerivationTrace_acceptance
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    AcceptanceTrace
      (FiniteProductionListDerivationTrace G rules)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    exact (generalGrammar_derivationTrace_acceptance G w).mp
      ⟨n,
        (finiteProductionListDerivationTrace_iff_derivationTrace
          hrules).mp hn⟩
  · intro h
    rcases (generalGrammar_derivationTrace_acceptance G w).mpr h with
      ⟨n, hn⟩
    exact
      ⟨n,
        (finiteProductionListDerivationTrace_iff_derivationTrace
          hrules).mpr hn⟩

theorem finiteProductionListDerivationTrace_acceptance_of_hasFiniteProductions
    {G : GeneralGrammar terminal nonterminal}
    (hfinite : GeneralGrammar.HasFiniteProductions G) :
    exists rules : List (GeneralGrammar.Production terminal nonterminal),
      AcceptanceTrace
        (FiniteProductionListDerivationTrace G rules)
        (GeneralGrammar.GeneratedLanguage G) := by
  rcases GeneralGrammar.hasFiniteProductions_productionListProduces
    hfinite with ⟨rules, hrules⟩
  exact ⟨rules, finiteProductionListDerivationTrace_acceptance hrules⟩

noncomputable def GeneralGrammarRecognizerProgram
    (G : GeneralGrammar terminal nonterminal) :
    StagedProgram terminal Unit :=
  by
    classical
    exact
      { run := fun w n =>
          if GeneralGrammarDerivationTrace G w n then some [] else none }

theorem generalGrammarRecognizerProgram_run_of_trace
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal} {n : Nat}
    (h : GeneralGrammarDerivationTrace G w n) :
    (GeneralGrammarRecognizerProgram G).run w n = some [] := by
  classical
  simp [GeneralGrammarRecognizerProgram, h]
  rfl

noncomputable def FiniteProductionListRecognizerProgram
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  by
    classical
    exact
      { run := fun w n =>
          if FiniteProductionListDerivationTrace G rules w n then
            some []
          else
            none }

theorem finiteProductionListRecognizerProgram_run_of_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat}
    (h : FiniteProductionListDerivationTrace G rules w n) :
    (FiniteProductionListRecognizerProgram G rules).run w n = some [] := by
  classical
  simp [FiniteProductionListRecognizerProgram, h]
  rfl

theorem generalGrammarRecognizerProgram_acceptsLanguage
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarRecognizerProgram G)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  constructor
  · intro h
    cases h with
    | intro n hn =>
        by_cases htrace : GeneralGrammarDerivationTrace G w n
        · exact (generalGrammar_derivationTrace_acceptance G w).mp
            (Exists.intro n htrace)
        · simp [GeneralGrammarRecognizerProgram, htrace] at hn
  · intro h
    cases (generalGrammar_derivationTrace_acceptance G w).mpr h with
    | intro n hn =>
        exact Exists.intro n
          (generalGrammarRecognizerProgram_run_of_trace hn)

theorem finiteProductionListRecognizerProgram_acceptsLanguage
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    by_cases htrace : FiniteProductionListDerivationTrace G rules w n
    · exact (finiteProductionListDerivationTrace_acceptance hrules w).mp
        ⟨n, htrace⟩
    · simp [FiniteProductionListRecognizerProgram, htrace] at hn
  · intro h
    rcases (finiteProductionListDerivationTrace_acceptance hrules w).mpr h with
      ⟨n, hn⟩
    exact ⟨n, finiteProductionListRecognizerProgram_run_of_trace hn⟩

theorem finiteProductionListRecognizerProgram_acceptsLanguage_of_hasFiniteProductions
    {G : GeneralGrammar terminal nonterminal}
    (hfinite : GeneralGrammar.HasFiniteProductions G) :
    exists rules : List (GeneralGrammar.Production terminal nonterminal),
      ProgramAcceptsLanguage
        (FiniteProductionListRecognizerProgram G rules)
        (GeneralGrammar.GeneratedLanguage G) := by
  rcases GeneralGrammar.hasFiniteProductions_productionListProduces
    hfinite with ⟨rules, hrules⟩
  exact ⟨rules, finiteProductionListRecognizerProgram_acceptsLanguage hrules⟩

theorem generalGrammar_generatedLanguage_programAcceptable
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptable (GeneralGrammar.GeneratedLanguage G) :=
  Exists.intro (GeneralGrammarRecognizerProgram G)
    (generalGrammarRecognizerProgram_acceptsLanguage G)

theorem generalGrammar_generated_programAcceptable
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    ProgramAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact programAcceptable_of_equal
            (generalGrammar_generatedLanguage_programAcceptable G) hG

theorem finiteProductionGenerated_programAcceptable
    {L : Language terminal}
    (h : GeneralGrammar.FiniteProductionGenerated L) :
    ProgramAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact programAcceptable_of_equal
            (generalGrammar_generatedLanguage_programAcceptable G)
            hG.right

theorem generalGrammar_generatedLanguage_recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    (G : GeneralGrammar terminal nonterminal) :
    RecursivelyEnumerable (GeneralGrammar.GeneratedLanguage G) :=
  recursivelyEnumerable_of_programCompiler hcompile
    (generalGrammar_generatedLanguage_programAcceptable G)

theorem generalGrammar_generated_recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    RecursivelyEnumerable L :=
  recursivelyEnumerable_of_programCompiler hcompile
    (generalGrammar_generated_programAcceptable h)

theorem finiteProductionGenerated_recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.FiniteProductionGenerated L) :
    RecursivelyEnumerable L :=
  recursivelyEnumerable_of_programCompiler hcompile
    (finiteProductionGenerated_programAcceptable h)

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

/-!
# Chapter 5 grammar construction boundaries

The textbook equivalence between unrestricted grammars and recursively
enumerable languages contains two construction-heavy directions. The recognizer
direction is proved at the staged-program layer above. The definitions below
name the remaining concrete compiler surfaces for Boolean machine descriptions.
The semantic reverse direction is no longer a construction boundary: with
arbitrary production predicates, every language has a one-nonterminal grammar.
-/

def BooleanGeneralGrammarRecognizerCompilerPrinciple : Prop :=
  forall {nonterminal : Type}, forall G : GeneralGrammar Bool nonterminal,
    exists D : MachineDescription,
      ProgramCompiledByDescription (GeneralGrammarRecognizerProgram G) D

def FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple : Prop :=
  forall {nonterminal : Type}, forall G : GeneralGrammar Bool nonterminal,
    GeneralGrammar.HasFiniteProductions G ->
      exists D : MachineDescription,
        ProgramCompiledByDescription (GeneralGrammarRecognizerProgram G) D

def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L <-> RecursivelyEnumerable L

def GeneralGrammarToRecursivelyEnumerablePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    GeneralGrammar.Generated L -> RecursivelyEnumerable L

def RecursivelyEnumerableToGeneralGrammarPrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    RecursivelyEnumerable L -> GeneralGrammar.Generated L

def RecursivelyEnumerableToFiniteGeneralGrammarPrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    RecursivelyEnumerable L -> GeneralGrammar.FiniteProductionGenerated L

def GeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    GeneralGrammarAcceptabilityEquivalence L

def FiniteGeneralGrammarAcceptabilityEquivalence
    (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L <-> RecursivelyEnumerable L

def FiniteGeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FiniteGeneralGrammarAcceptabilityEquivalence L

structure BooleanSection52CompilerCloseout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  dovetailDescription : DovetailDescriptionCompilerPrinciple
  partialUnaryRangeDescription :
    PartialUnaryRangeDescriptionCompilerPrinciple
  grammarRecognizerDescription :
    BooleanGeneralGrammarRecognizerCompilerPrinciple

structure BooleanFiniteGrammarSection52Closeout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  dovetailDescription : DovetailDescriptionCompilerPrinciple
  partialUnaryRangeDescription :
    PartialUnaryRangeDescriptionCompilerPrinciple
  finiteGrammarRecognizerDescription :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple
  recursivelyEnumerableToFiniteGrammar :
    RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool

end Computability
end FoC

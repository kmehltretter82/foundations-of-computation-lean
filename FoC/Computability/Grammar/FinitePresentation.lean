import FoC.Computability.Grammar.DerivationTraces

set_option doc.verso true

/-!
# Finite Boolean grammar presentations
-/

namespace FoC
namespace Computability

open Languages
open Grammars

/-!
## First-order finite Boolean grammar presentations

The finite-production recognizer above is still parameterized by an arbitrary
Lean nonterminal type.  For concrete compiler construction, the finite source
syntax should expose the nonterminals as first-order data.  The presentation
below fixes the nonterminal type to {lit}`Fin n`, stores a finite production
list, and records the unrestricted-grammar left-side side condition for every
listed rule.
-/

structure FiniteBoolGeneralGrammarPresentation where
  nonterminalCount : Nat
  start : Fin nonterminalCount
  rules : List (GeneralGrammar.Production Bool (Fin nonterminalCount))
  rule_lhsContainsNonterminal :
    forall rule : GeneralGrammar.Production Bool (Fin nonterminalCount),
      rule ∈ rules -> SententialForm.containsNonterminal rule.lhs

namespace FiniteBoolGeneralGrammarPresentation

noncomputable def indexOf {α : Type}
    (finite : Foundation.FiniteType α) (a : α) :
    Fin finite.elems.length :=
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = a :=
    (List.mem_iff_getElem).mp (finite.complete a)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

def valueOf {α : Type}
    (finite : Foundation.FiniteType α)
    (i : Fin finite.elems.length) : α :=
  finite.elems[i]

theorem valueOf_indexOf {α : Type}
    (finite : Foundation.FiniteType α) (a : α) :
    valueOf finite (indexOf finite a) = a := by
  unfold valueOf indexOf
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = a :=
    (List.mem_iff_getElem).mp (finite.complete a)
  exact Classical.choose_spec (Classical.choose_spec h)

def indexOfDecidable {α : Type} [DecidableEq α]
    (finite : Foundation.FiniteType α) (a : α) :
    Fin finite.elems.length :=
  Foundation.FiniteType.indexOfDecidable finite a

theorem valueOf_indexOfDecidable {α : Type} [DecidableEq α]
    (finite : Foundation.FiniteType α) (a : α) :
    valueOf finite (indexOfDecidable finite a) = a := by
  simpa [valueOf, indexOfDecidable, Foundation.FiniteType.valueOf]
    using Foundation.FiniteType.valueOf_indexOfDecidable finite a

def mapProduction
    (f : nonterminal -> nonterminal')
    (rule : GeneralGrammar.Production terminal nonterminal) :
    GeneralGrammar.Production terminal nonterminal' where
  lhs := SententialForm.mapNonterminal f rule.lhs
  rhs := SententialForm.mapNonterminal f rule.rhs

theorem containsNonterminal_mapNonterminal_iff
    (f : nonterminal -> nonterminal')
    (form : SententialForm terminal nonterminal) :
    SententialForm.containsNonterminal
        (SententialForm.mapNonterminal f form) <->
      SententialForm.containsNonterminal form := by
  induction form with
  | nil =>
      simp [SententialForm.mapNonterminal,
        SententialForm.containsNonterminal]
  | cons symbol rest ih =>
      cases symbol with
      | terminal _ =>
          simpa [SententialForm.mapNonterminal,
            Symbol.mapNonterminal,
            SententialForm.containsNonterminal] using ih
      | nonterminal _ =>
          simp [SententialForm.mapNonterminal, Symbol.mapNonterminal,
            SententialForm.containsNonterminal]

theorem mapNonterminal_valueOf_indexOf
    {α : Type}
    (finite : Foundation.FiniteType α)
    (form : SententialForm terminal α) :
    SententialForm.mapNonterminal (valueOf finite)
        (SententialForm.mapNonterminal (indexOf finite) form) =
      form := by
  induction form with
  | nil =>
      rfl
  | cons symbol rest ih =>
      cases symbol with
      | terminal _ =>
          simp [SententialForm.mapNonterminal, Symbol.mapNonterminal]
          simpa [SententialForm.mapNonterminal, List.map_map] using ih
      | nonterminal _ =>
          simp [SententialForm.mapNonterminal, Symbol.mapNonterminal,
            valueOf_indexOf]
          simpa [SententialForm.mapNonterminal, List.map_map] using ih

theorem mapNonterminal_valueOf_indexOfDecidable
    {α : Type} [DecidableEq α]
    (finite : Foundation.FiniteType α)
    (form : SententialForm terminal α) :
    SententialForm.mapNonterminal (valueOf finite)
        (SententialForm.mapNonterminal (indexOfDecidable finite) form) =
      form := by
  induction form with
  | nil =>
      rfl
  | cons symbol rest ih =>
      cases symbol with
      | terminal _ =>
          simp [SententialForm.mapNonterminal, Symbol.mapNonterminal]
          simpa [SententialForm.mapNonterminal, List.map_map] using ih
      | nonterminal _ =>
          simp [SententialForm.mapNonterminal, Symbol.mapNonterminal,
            valueOf_indexOfDecidable]
          simpa [SententialForm.mapNonterminal, List.map_map] using ih

def toGrammar (P : FiniteBoolGeneralGrammarPresentation) :
    GeneralGrammar Bool (Fin P.nonterminalCount) where
  start := P.start
  produces := GeneralGrammar.ProductionListProduces P.rules
  lhsContainsNonterminal := by
    intro lhs rhs h
    rcases h with ⟨rule, hrule, hlhs, _hrhs⟩
    rw [← hlhs]
    exact P.rule_lhsContainsNonterminal rule hrule
  nonterminalsFinite := Foundation.FiniteType.fin P.nonterminalCount

theorem toGrammar_produces_iff
    (P : FiniteBoolGeneralGrammarPresentation)
    (lhs rhs : SententialForm Bool (Fin P.nonterminalCount)) :
    P.toGrammar.produces lhs rhs <->
      GeneralGrammar.ProductionListProduces P.rules lhs rhs :=
  Iff.rfl

/-- The first-order Boolean grammar data gives an exact proof-relevant
presentation of its semantic grammar. -/
def toPresentation (P : FiniteBoolGeneralGrammarPresentation) :
    GeneralGrammar.Presentation P.toGrammar where
  rules := P.rules
  complete := P.toGrammar_produces_iff

theorem toGrammar_hasFinitePresentation
    (P : FiniteBoolGeneralGrammarPresentation) :
    GeneralGrammar.HasFinitePresentation P.toGrammar :=
  P.toPresentation.hasFinitePresentation

theorem toGrammar_hasFiniteProductions
    (P : FiniteBoolGeneralGrammarPresentation) :
    GeneralGrammar.HasFiniteProductions P.toGrammar :=
  P.toPresentation.hasFiniteProductions

noncomputable def recognizerProgram
    (P : FiniteBoolGeneralGrammarPresentation) :
    StagedProgram Bool Unit :=
  FinitePresentationRecognizerProgram P.toPresentation

theorem recognizerProgram_acceptsLanguage
    (P : FiniteBoolGeneralGrammarPresentation) :
    ProgramAcceptsLanguage P.recognizerProgram
      (GeneralGrammar.GeneratedLanguage P.toGrammar) :=
  finitePresentationRecognizerProgram_acceptsLanguage P.toPresentation

def CompilerConstruction : Prop :=
  forall P : FiniteBoolGeneralGrammarPresentation,
    exists D : MachineDescription,
      ProgramCompiledByDescription P.recognizerProgram D

def BoundedRecognizerCompilerConstruction : Prop :=
  forall P : FiniteBoolGeneralGrammarPresentation,
    exists D : MachineDescription,
      ProgramCompiledByDescription
        (FinitePresentationBoundedRecognizerProgram P.toPresentation) D

def CertificateRecognizerCompilerConstruction : Prop :=
  forall P : FiniteBoolGeneralGrammarPresentation,
    exists D : MachineDescription,
      ProgramCompiledByDescription
        (FinitePresentationCertificateRecognizerProgram P.toPresentation) D

def IndexedCertificateRecognizerCompilerConstruction : Prop :=
  forall P : FiniteBoolGeneralGrammarPresentation,
    exists D : MachineDescription,
      ProgramCompiledByDescription
        (FinitePresentationIndexedCertificateRecognizerProgram
          P.toPresentation) D

def CheckedIndexedCertificateRecognizerCompilerConstruction : Prop :=
  forall P : FiniteBoolGeneralGrammarPresentation,
    exists D : MachineDescription,
      ProgramCompiledByDescription
        (FinitePresentationCheckedIndexedCertificateRecognizerProgram
          P.toPresentation) D

theorem compilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    CompilerConstruction := by
  intro P
  exact hcompile P.recognizerProgram

theorem certificateRecognizerCompilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    CertificateRecognizerCompilerConstruction := by
  intro P
  exact
    hcompile
      (FinitePresentationCertificateRecognizerProgram P.toPresentation)

theorem indexedCertificateRecognizerCompilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    IndexedCertificateRecognizerCompilerConstruction := by
  intro P
  exact
    hcompile
      (FinitePresentationIndexedCertificateRecognizerProgram
        P.toPresentation)

theorem checkedIndexedCertificateRecognizerCompilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    CheckedIndexedCertificateRecognizerCompilerConstruction := by
  intro P
  exact
    hcompile
      (FinitePresentationCheckedIndexedCertificateRecognizerProgram
        P.toPresentation)

theorem boundedRecognizerCompilerConstruction_of_certificateRecognizerCompiler
    (hcompile : CertificateRecognizerCompilerConstruction) :
    BoundedRecognizerCompilerConstruction := by
  intro P
  rcases hcompile P with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finitePresentationCertificateRecognizerProgram_acceptsLanguage
          P.toPresentation)
        (finitePresentationBoundedRecognizerProgram_acceptsLanguage
          P.toPresentation)
        hD⟩

theorem boundedRecognizerCompilerConstruction_of_indexedCertificateRecognizerCompiler
    (hcompile : IndexedCertificateRecognizerCompilerConstruction) :
    BoundedRecognizerCompilerConstruction := by
  intro P
  rcases hcompile P with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finitePresentationIndexedCertificateRecognizerProgram_acceptsLanguage
          P.toPresentation)
        (finitePresentationBoundedRecognizerProgram_acceptsLanguage
          P.toPresentation)
        hD⟩

theorem indexedCertificateRecognizerCompilerConstruction_of_checkedIndexedCertificateRecognizerCompiler
    (hcompile : CheckedIndexedCertificateRecognizerCompilerConstruction) :
    IndexedCertificateRecognizerCompilerConstruction := by
  intro P
  rcases hcompile P with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finitePresentationCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
          P.toPresentation)
        (finitePresentationIndexedCertificateRecognizerProgram_acceptsLanguage
          P.toPresentation)
        hD⟩

theorem boundedRecognizerCompilerConstruction_of_checkedIndexedCertificateRecognizerCompiler
    (hcompile : CheckedIndexedCertificateRecognizerCompilerConstruction) :
    BoundedRecognizerCompilerConstruction :=
  boundedRecognizerCompilerConstruction_of_indexedCertificateRecognizerCompiler
    (indexedCertificateRecognizerCompilerConstruction_of_checkedIndexedCertificateRecognizerCompiler
      hcompile)

theorem compilerConstruction_of_boundedRecognizerCompiler
    (hcompile : BoundedRecognizerCompilerConstruction) :
    CompilerConstruction := by
  intro P
  rcases hcompile P with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finitePresentationBoundedRecognizerProgram_acceptsLanguage
          P.toPresentation)
        P.recognizerProgram_acceptsLanguage
        hD⟩

def ofGrammarRules [DecidableEq nonterminal]
    (G : GeneralGrammar Bool nonterminal)
    (rules : List (GeneralGrammar.Production Bool nonterminal))
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    FiniteBoolGeneralGrammarPresentation where
  nonterminalCount := G.nonterminalsFinite.elems.length
  start := indexOfDecidable G.nonterminalsFinite G.start
  rules := rules.map (mapProduction (indexOfDecidable G.nonterminalsFinite))
  rule_lhsContainsNonterminal := by
    intro rule hrule
    rcases List.mem_map.mp hrule with ⟨source, hsource, rfl⟩
    have hprod : G.produces source.lhs source.rhs :=
      (hrules source.lhs source.rhs).mpr
        ⟨source, hsource, rfl, rfl⟩
    exact
      (containsNonterminal_mapNonterminal_iff
        (indexOfDecidable G.nonterminalsFinite) source.lhs).mpr
        (G.lhsContainsNonterminal source.lhs source.rhs hprod)

/-- Replace an arbitrary finite nonterminal type by {lit}`Fin n`, retaining the
rule list and exactness theorem from an explicit presentation. -/
def ofPresentation [DecidableEq nonterminal]
    {G : GeneralGrammar Bool nonterminal}
    (presentation : GeneralGrammar.Presentation G) :
    FiniteBoolGeneralGrammarPresentation :=
  ofGrammarRules G presentation.rules presentation.complete

theorem productionListYields_mapNonterminal
    (f : nonterminal -> nonterminal')
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x y : SententialForm terminal nonterminal}
    (h : GeneralGrammar.ProductionListYields rules x y) :
    GeneralGrammar.ProductionListYields
      (rules.map (mapProduction f))
      (SententialForm.mapNonterminal f x)
      (SententialForm.mapNonterminal f y) := by
  rcases h with ⟨u, v, rule, hrule, hx, hy⟩
  refine
    ⟨SententialForm.mapNonterminal f u,
      SententialForm.mapNonterminal f v,
      mapProduction f rule, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨rule, hrule, rfl⟩
  · simp [hx, mapProduction, SententialForm.mapNonterminal_append]
  · simp [hy, mapProduction, SententialForm.mapNonterminal_append]

theorem productionListDerivesIn_mapNonterminal
    (f : nonterminal -> nonterminal')
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat}
    {x y : SententialForm terminal nonterminal}
    (h : GeneralGrammar.ProductionListDerivesIn rules n x y) :
    GeneralGrammar.ProductionListDerivesIn
      (rules.map (mapProduction f)) n
      (SententialForm.mapNonterminal f x)
      (SententialForm.mapNonterminal f y) := by
  induction h with
  | zero x =>
      exact GeneralGrammar.ProductionListDerivesIn.zero
        (SententialForm.mapNonterminal f x)
  | step hstep _hrest ih =>
      exact GeneralGrammar.ProductionListDerivesIn.step
        (productionListYields_mapNonterminal f hstep) ih

theorem productionListYields_unmap_indexOf
    {α : Type}
    (finite : Foundation.FiniteType α)
    {rules : List (GeneralGrammar.Production terminal α)}
    {x y : SententialForm terminal (Fin finite.elems.length)}
    (h :
      GeneralGrammar.ProductionListYields
        (rules.map (mapProduction (indexOf finite))) x y) :
    GeneralGrammar.ProductionListYields rules
      (SententialForm.mapNonterminal (valueOf finite) x)
      (SententialForm.mapNonterminal (valueOf finite) y) := by
  rcases h with ⟨u, v, rule, hrule, hx, hy⟩
  rcases List.mem_map.mp hrule with ⟨source, hsource, hsourceEq⟩
  refine
    ⟨SententialForm.mapNonterminal (valueOf finite) u,
      SententialForm.mapNonterminal (valueOf finite) v,
      source, hsource, ?_, ?_⟩
  · rw [hx, ← hsourceEq]
    simp [mapProduction, SententialForm.mapNonterminal_append,
      mapNonterminal_valueOf_indexOf]
  · rw [hy, ← hsourceEq]
    simp [mapProduction, SententialForm.mapNonterminal_append,
      mapNonterminal_valueOf_indexOf]

theorem productionListDerivesIn_unmap_indexOf
    {α : Type}
    (finite : Foundation.FiniteType α)
    {rules : List (GeneralGrammar.Production terminal α)}
    {n : Nat}
    {x y : SententialForm terminal (Fin finite.elems.length)}
    (h :
      GeneralGrammar.ProductionListDerivesIn
        (rules.map (mapProduction (indexOf finite))) n x y) :
    GeneralGrammar.ProductionListDerivesIn rules n
      (SententialForm.mapNonterminal (valueOf finite) x)
      (SententialForm.mapNonterminal (valueOf finite) y) := by
  induction h with
  | zero x =>
      exact GeneralGrammar.ProductionListDerivesIn.zero
        (SententialForm.mapNonterminal (valueOf finite) x)
  | step hstep _hrest ih =>
      exact GeneralGrammar.ProductionListDerivesIn.step
        (productionListYields_unmap_indexOf finite hstep) ih

theorem productionListYields_unmap_indexOfDecidable
    {α : Type} [DecidableEq α]
    (finite : Foundation.FiniteType α)
    {rules : List (GeneralGrammar.Production terminal α)}
    {x y : SententialForm terminal (Fin finite.elems.length)}
    (h :
      GeneralGrammar.ProductionListYields
        (rules.map (mapProduction (indexOfDecidable finite))) x y) :
    GeneralGrammar.ProductionListYields rules
      (SententialForm.mapNonterminal (valueOf finite) x)
      (SententialForm.mapNonterminal (valueOf finite) y) := by
  rcases h with ⟨u, v, rule, hrule, hx, hy⟩
  rcases List.mem_map.mp hrule with ⟨source, hsource, hsourceEq⟩
  refine
    ⟨SententialForm.mapNonterminal (valueOf finite) u,
      SententialForm.mapNonterminal (valueOf finite) v,
      source, hsource, ?_, ?_⟩
  · rw [hx, ← hsourceEq]
    simp [mapProduction, SententialForm.mapNonterminal_append,
      mapNonterminal_valueOf_indexOfDecidable]
  · rw [hy, ← hsourceEq]
    simp [mapProduction, SententialForm.mapNonterminal_append,
      mapNonterminal_valueOf_indexOfDecidable]

theorem productionListDerivesIn_unmap_indexOfDecidable
    {α : Type} [DecidableEq α]
    (finite : Foundation.FiniteType α)
    {rules : List (GeneralGrammar.Production terminal α)}
    {n : Nat}
    {x y : SententialForm terminal (Fin finite.elems.length)}
    (h :
      GeneralGrammar.ProductionListDerivesIn
        (rules.map (mapProduction (indexOfDecidable finite))) n x y) :
    GeneralGrammar.ProductionListDerivesIn rules n
      (SententialForm.mapNonterminal (valueOf finite) x)
      (SententialForm.mapNonterminal (valueOf finite) y) := by
  induction h with
  | zero x =>
      exact GeneralGrammar.ProductionListDerivesIn.zero
        (SententialForm.mapNonterminal (valueOf finite) x)
  | step hstep _hrest ih =>
      exact GeneralGrammar.ProductionListDerivesIn.step
        (productionListYields_unmap_indexOfDecidable finite hstep) ih

theorem generatedLanguage_equal_ofGrammarRules [DecidableEq nonterminal]
    (G : GeneralGrammar Bool nonterminal)
    (rules : List (GeneralGrammar.Production Bool nonterminal))
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (ofGrammarRules G rules hrules).toGrammar)
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  let P := ofGrammarRules G rules hrules
  constructor
  · intro hP
    rcases GeneralGrammar.derives_derivesIn hP with ⟨n, hPDerives⟩
    have hPList :
        GeneralGrammar.ProductionListDerivesIn P.rules n
          [Symbol.nonterminal P.start]
          (SententialForm.terminalWord w) :=
      (GeneralGrammar.productionListDerivesIn_iff_derivesIn_of_produces
        (P.toGrammar_produces_iff)).mpr hPDerives
    have hUnmapped :=
      productionListDerivesIn_unmap_indexOfDecidable G.nonterminalsFinite
        (rules := rules) hPList
    have hGList :
        GeneralGrammar.ProductionListDerivesIn rules n
          [Symbol.nonterminal G.start]
          (SententialForm.terminalWord w) := by
      have hStart :
          SententialForm.mapNonterminal (term := Bool)
              (valueOf G.nonterminalsFinite)
              ([Symbol.nonterminal (terminal := Bool)
                (indexOfDecidable G.nonterminalsFinite G.start)] :
                SententialForm Bool
                  (Fin G.nonterminalsFinite.elems.length)) =
            ([Symbol.nonterminal (terminal := Bool) G.start] :
              SententialForm Bool nonterminal) := by
        simp [SententialForm.mapNonterminal, Symbol.mapNonterminal,
          valueOf_indexOfDecidable]
      have hTerm :
          SententialForm.mapNonterminal (term := Bool)
              (valueOf G.nonterminalsFinite)
              (SententialForm.terminalWord
                (nt := Fin G.nonterminalsFinite.elems.length) w) =
            SententialForm.terminalWord (nt := nonterminal) w :=
        SententialForm.mapNonterminal_terminalWord
          (valueOf G.nonterminalsFinite) w
      simpa [P, ofGrammarRules, hStart, hTerm] using hUnmapped
    exact GeneralGrammar.derivesIn_derives
      ((GeneralGrammar.productionListDerivesIn_iff_derivesIn_of_produces
        hrules).mp hGList)
  · intro hG
    rcases GeneralGrammar.derives_derivesIn hG with ⟨n, hGDerives⟩
    have hGList :
        GeneralGrammar.ProductionListDerivesIn rules n
          [Symbol.nonterminal G.start]
          (SententialForm.terminalWord w) :=
      (GeneralGrammar.productionListDerivesIn_iff_derivesIn_of_produces
        hrules).mpr hGDerives
    have hMapped :=
      productionListDerivesIn_mapNonterminal
        (indexOfDecidable G.nonterminalsFinite) hGList
    have hPList :
        GeneralGrammar.ProductionListDerivesIn P.rules n
          [Symbol.nonterminal P.start]
          (SententialForm.terminalWord w) := by
      simpa [P, ofGrammarRules,
        SententialForm.mapNonterminal_terminalWord] using! hMapped
    exact GeneralGrammar.derivesIn_derives
      ((GeneralGrammar.productionListDerivesIn_iff_derivesIn_of_produces
        (P.toGrammar_produces_iff)).mp hPList)

theorem generatedLanguage_equal_ofPresentation [DecidableEq nonterminal]
    {G : GeneralGrammar Bool nonterminal}
    (presentation : GeneralGrammar.Presentation G) :
    Language.Equal
      (GeneralGrammar.GeneratedLanguage
        (ofPresentation presentation).toGrammar)
      (GeneralGrammar.GeneratedLanguage G) :=
  generatedLanguage_equal_ofGrammarRules G presentation.rules
    presentation.complete

theorem recognizerProgram_acceptsLanguage_ofGrammarRules
    [DecidableEq nonterminal]
    (G : GeneralGrammar Bool nonterminal)
    (rules : List (GeneralGrammar.Production Bool nonterminal))
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (ofGrammarRules G rules hrules).recognizerProgram
      (GeneralGrammar.GeneratedLanguage G) := by
  intro w
  exact Iff.trans
    ((ofGrammarRules G rules hrules).recognizerProgram_acceptsLanguage w)
    ((generatedLanguage_equal_ofGrammarRules G rules hrules) w)

theorem recognizerProgram_acceptsLanguage_ofPresentation
    [DecidableEq nonterminal]
    {G : GeneralGrammar Bool nonterminal}
    (presentation : GeneralGrammar.Presentation G) :
    ProgramAcceptsLanguage
      (ofPresentation presentation).recognizerProgram
      (GeneralGrammar.GeneratedLanguage G) :=
  recognizerProgram_acceptsLanguage_ofGrammarRules G presentation.rules
    presentation.complete

end FiniteBoolGeneralGrammarPresentation

def FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentation.CompilerConstruction

def FiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentation.BoundedRecognizerCompilerConstruction

def FiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentation.CertificateRecognizerCompilerConstruction

def FiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentation.IndexedCertificateRecognizerCompilerConstruction

def FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction :
    Prop :=
  FiniteBoolGeneralGrammarPresentation.CheckedIndexedCertificateRecognizerCompilerConstruction

namespace FiniteBoolGeneralGrammarPresentation

namespace RecognizerCompilerConstruction

theorem of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.compilerConstruction_of_descriptionCompiler
    hcompile

end RecognizerCompilerConstruction

namespace CertificateRecognizerCompilerConstruction

theorem of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.certificateRecognizerCompilerConstruction_of_descriptionCompiler
    hcompile

end CertificateRecognizerCompilerConstruction

namespace IndexedCertificateRecognizerCompilerConstruction

theorem of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.indexedCertificateRecognizerCompilerConstruction_of_descriptionCompiler
    hcompile

theorem of_checkedIndexedCertificateRecognizerCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.indexedCertificateRecognizerCompilerConstruction_of_checkedIndexedCertificateRecognizerCompiler
    hcompile

end IndexedCertificateRecognizerCompilerConstruction

namespace CheckedIndexedCertificateRecognizerCompilerConstruction

theorem of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.checkedIndexedCertificateRecognizerCompilerConstruction_of_descriptionCompiler
    hcompile

/-!
**Finite-source handoff.**  The remaining finite grammar compiler target is a
first-order certificate checker for an explicit finite production-list
presentation.  The scaffold declarations below no longer manufacture that
compiler.  They expose the finite dependency graph: once a checked-indexed
certificate compiler is supplied, the existing equivalence bridges derive the
indexed, bounded, and full presentation recognizers.
-/

theorem scaffold
    (hcompile :
      FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction :=
  hcompile

end CheckedIndexedCertificateRecognizerCompilerConstruction

namespace BoundedRecognizerCompilerConstruction

theorem of_certificateRecognizerCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationCertificateRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.boundedRecognizerCompilerConstruction_of_certificateRecognizerCompiler
    hcompile

theorem of_indexedCertificateRecognizerCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationIndexedCertificateRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.boundedRecognizerCompilerConstruction_of_indexedCertificateRecognizerCompiler
    hcompile

theorem of_checkedIndexedCertificateRecognizerCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.boundedRecognizerCompilerConstruction_of_checkedIndexedCertificateRecognizerCompiler
    hcompile

end BoundedRecognizerCompilerConstruction

namespace RecognizerCompilerConstruction

theorem of_boundedRecognizerCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationBoundedRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  FiniteBoolGeneralGrammarPresentation.compilerConstruction_of_boundedRecognizerCompiler
    hcompile

theorem scaffold
    (hcompile :
      FiniteBoolGeneralGrammarPresentationCheckedIndexedCertificateRecognizerCompilerConstruction) :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction :=
  of_boundedRecognizerCompiler
    (BoundedRecognizerCompilerConstruction.of_checkedIndexedCertificateRecognizerCompiler
      (CheckedIndexedCertificateRecognizerCompilerConstruction.scaffold
        hcompile))

end RecognizerCompilerConstruction

end FiniteBoolGeneralGrammarPresentation

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

theorem finitePresentationGenerated_programAcceptable
    {L : Language terminal}
    (h : GeneralGrammar.FinitePresentationGenerated L) :
    ProgramAcceptable L := by
  cases h with
  | intro nonterminal hnonterminal =>
      cases hnonterminal with
      | intro G hG =>
          exact programAcceptable_of_equal
            (generalGrammar_generatedLanguage_programAcceptable G)
            hG.right

theorem finiteProductionGenerated_programAcceptable
    {L : Language terminal}
    (h : GeneralGrammar.FiniteProductionGenerated L) :
    ProgramAcceptable L :=
  finitePresentationGenerated_programAcceptable
    (GeneralGrammar.finitePresentationGenerated_iff_finiteProductionGenerated.mpr
      h)

theorem generalGrammar_generatedLanguage_turingAcceptable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    (G : GeneralGrammar terminal nonterminal) :
    TuringAcceptable (GeneralGrammar.GeneratedLanguage G) :=
  turingAcceptable_of_programCompiler hcompile
    (generalGrammar_generatedLanguage_programAcceptable G)

theorem generalGrammar_generated_turingAcceptable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.Generated L) :
    TuringAcceptable L :=
  turingAcceptable_of_programCompiler hcompile
    (generalGrammar_generated_programAcceptable h)

theorem finitePresentationGenerated_turingAcceptable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.FinitePresentationGenerated L) :
    TuringAcceptable L :=
  turingAcceptable_of_programCompiler hcompile
    (finitePresentationGenerated_programAcceptable h)

theorem finiteProductionGenerated_turingAcceptable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple terminal)
    {L : Language terminal}
    (h : GeneralGrammar.FiniteProductionGenerated L) :
    TuringAcceptable L :=
  finitePresentationGenerated_turingAcceptable_of_programCompiler
    hcompile
    (GeneralGrammar.finitePresentationGenerated_iff_finiteProductionGenerated.mpr
      h)


end Computability
end FoC

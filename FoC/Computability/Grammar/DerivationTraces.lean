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

inductive FiniteProductionListStepCertificate
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (x y : SententialForm terminal nonterminal) : Prop where
  | intro
      (pre : SententialForm terminal nonterminal)
      (suf : SententialForm terminal nonterminal)
      (rule : GeneralGrammar.Production terminal nonterminal) :
      rule ∈ rules ->
      x = pre ++ rule.lhs ++ suf ->
      y = pre ++ rule.rhs ++ suf ->
      FiniteProductionListStepCertificate rules x y

theorem FiniteProductionListStepCertificate.to_yields
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x y : SententialForm terminal nonterminal}
    (cert : FiniteProductionListStepCertificate rules x y) :
    GeneralGrammar.ProductionListYields rules x y := by
  rcases cert with ⟨pre, suf, rule, hrule, hsource, htarget⟩
  exact ⟨pre, suf, rule, hrule, hsource, htarget⟩

theorem FiniteProductionListStepCertificate.of_yields
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x y : SententialForm terminal nonterminal}
    (h : GeneralGrammar.ProductionListYields rules x y) :
    FiniteProductionListStepCertificate rules x y := by
  rcases h with ⟨pre, suf, rule, hrule, hsource, htarget⟩
  exact FiniteProductionListStepCertificate.intro
    pre suf rule hrule hsource htarget

structure FiniteProductionListIndexedStepCertificate
    (rules : List (GeneralGrammar.Production terminal nonterminal)) where
  pre : SententialForm terminal nonterminal
  suf : SententialForm terminal nonterminal
  ruleIndex : Fin rules.length

namespace FiniteProductionListIndexedStepCertificate

def Matches
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (cert : FiniteProductionListIndexedStepCertificate rules)
    (x y : SententialForm terminal nonterminal) : Prop :=
  x = cert.pre ++ (rules.get cert.ruleIndex).lhs ++ cert.suf ∧
    y = cert.pre ++ (rules.get cert.ruleIndex).rhs ++ cert.suf

theorem to_stepCertificate
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x y : SententialForm terminal nonterminal}
    (cert : FiniteProductionListIndexedStepCertificate rules)
    (hmatch : cert.Matches x y) :
    FiniteProductionListStepCertificate rules x y :=
  FiniteProductionListStepCertificate.intro
    cert.pre cert.suf (rules.get cert.ruleIndex)
    (List.get_mem rules cert.ruleIndex)
    hmatch.left hmatch.right

theorem exists_of_stepCertificate
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x y : SententialForm terminal nonterminal}
    (cert : FiniteProductionListStepCertificate rules x y) :
    exists indexed : FiniteProductionListIndexedStepCertificate rules,
      indexed.Matches x y := by
  rcases cert with ⟨pre, suf, rule, hrule, hsource, htarget⟩
  rcases (List.mem_iff_get.mp hrule) with ⟨ruleIndex, hindex⟩
  refine
    ⟨{ pre := pre, suf := suf, ruleIndex := ruleIndex }, ?_⟩
  cases hindex
  simp [Matches, hsource, htarget]

theorem exists_iff_stepCertificate
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x y : SententialForm terminal nonterminal} :
    (exists indexed : FiniteProductionListIndexedStepCertificate rules,
      indexed.Matches x y) <->
      FiniteProductionListStepCertificate rules x y := by
  constructor
  · intro h
    rcases h with ⟨indexed, hmatch⟩
    exact indexed.to_stepCertificate hmatch
  · exact exists_of_stepCertificate

def check [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (cert : FiniteProductionListIndexedStepCertificate rules)
    (x y : SententialForm terminal nonterminal) : Bool :=
  decide (x = cert.pre ++ (rules.get cert.ruleIndex).lhs ++ cert.suf) &&
    decide (y = cert.pre ++ (rules.get cert.ruleIndex).rhs ++ cert.suf)

theorem check_eq_true_iff
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (cert : FiniteProductionListIndexedStepCertificate rules)
    (x y : SententialForm terminal nonterminal) :
    cert.check x y = true <-> cert.Matches x y := by
  simp [check, Matches]

end FiniteProductionListIndexedStepCertificate

def listAny {α : Type u} (p : α -> Bool) : List α -> Bool
  | [] => false
  | x :: xs => p x || listAny p xs

theorem listAny_eq_true_iff {α : Type u} (p : α -> Bool) :
    forall xs : List α,
      listAny p xs = true <-> exists x, x ∈ xs ∧ p x = true
  | [] => by
      simp [listAny]
  | x :: xs => by
      simp [listAny, listAny_eq_true_iff p xs]

def sententialFormSplits {α : Type u} : List α -> List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
      ([], x :: xs) ::
        (sententialFormSplits xs).map
          (fun split => (x :: split.1, split.2))

theorem sententialFormSplits_complete {α : Type u}
    (pre suf : List α) :
    (pre, suf) ∈ sententialFormSplits (pre ++ suf) := by
  induction pre with
  | nil =>
      cases suf <;> simp [sententialFormSplits]
  | cons x pre ih =>
      simp [sententialFormSplits, ih]

structure FiniteProductionListIndexedStepSearchCandidate
    (rules : List (GeneralGrammar.Production terminal nonterminal)) where
  mid : SententialForm terminal nonterminal
  cert : FiniteProductionListIndexedStepCertificate rules

def finiteProductionListIndexedStepSearchCandidates
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (x : SententialForm terminal nonterminal) :
    List (FiniteProductionListIndexedStepSearchCandidate rules) :=
  (List.finRange rules.length).flatMap fun ruleIndex =>
    (sententialFormSplits x).flatMap fun outerSplit =>
      (sententialFormSplits outerSplit.2).map fun innerSplit =>
        let cert : FiniteProductionListIndexedStepCertificate rules :=
          { pre := outerSplit.1
            suf := innerSplit.2
            ruleIndex := ruleIndex }
        { mid := outerSplit.1 ++ (rules.get ruleIndex).rhs ++
            innerSplit.2
          cert := cert }

theorem finiteProductionListIndexedStepSearchCandidates_complete
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {x mid : SententialForm terminal nonterminal}
    (cert : FiniteProductionListIndexedStepCertificate rules)
    (hmatch : cert.Matches x mid) :
    { mid := mid, cert := cert } ∈
      finiteProductionListIndexedStepSearchCandidates rules x := by
  rcases cert with ⟨pre, suf, ruleIndex⟩
  rcases hmatch with ⟨hx, hmid⟩
  subst x
  subst mid
  apply List.mem_flatMap.mpr
  refine ⟨ruleIndex, List.mem_finRange ruleIndex, ?_⟩
  apply List.mem_flatMap.mpr
  refine
    ⟨(pre, (rules.get ruleIndex).lhs ++ suf), ?_, ?_⟩
  · simpa [List.append_assoc] using
      sententialFormSplits_complete pre
        ((rules.get ruleIndex).lhs ++ suf)
  apply List.mem_map.mpr
  refine
    ⟨((rules.get ruleIndex).lhs, suf),
      sententialFormSplits_complete (rules.get ruleIndex).lhs suf, ?_⟩
  rfl

inductive FiniteProductionListDerivationCertificate
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    Nat -> SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Prop where
  | zero (x : SententialForm terminal nonterminal) :
      FiniteProductionListDerivationCertificate rules 0 x x
  | step {n : Nat} {x y z : SententialForm terminal nonterminal} :
      FiniteProductionListStepCertificate rules x y ->
      FiniteProductionListDerivationCertificate rules n y z ->
      FiniteProductionListDerivationCertificate rules (n + 1) x z

theorem FiniteProductionListDerivationCertificate.to_derivesIn
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (cert :
      FiniteProductionListDerivationCertificate rules n x y) :
    GeneralGrammar.ProductionListDerivesIn rules n x y := by
  induction cert with
  | zero x =>
      exact GeneralGrammar.ProductionListDerivesIn.zero x
  | step hstep _ ih =>
      exact GeneralGrammar.ProductionListDerivesIn.step
        hstep.to_yields ih

theorem FiniteProductionListDerivationCertificate.of_derivesIn
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (h : GeneralGrammar.ProductionListDerivesIn rules n x y) :
    FiniteProductionListDerivationCertificate rules n x y := by
  induction h with
  | zero x =>
      exact FiniteProductionListDerivationCertificate.zero x
  | step hstep _ ih =>
      exact FiniteProductionListDerivationCertificate.step
        (FiniteProductionListStepCertificate.of_yields hstep) ih

theorem finiteProductionListDerivationCertificate_iff_derivesIn
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal} :
    FiniteProductionListDerivationCertificate rules n x y <->
      GeneralGrammar.ProductionListDerivesIn rules n x y :=
  ⟨FiniteProductionListDerivationCertificate.to_derivesIn,
    FiniteProductionListDerivationCertificate.of_derivesIn⟩

inductive FiniteProductionListIndexedDerivationCertificate
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    Nat -> SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Prop where
  | zero (x : SententialForm terminal nonterminal) :
      FiniteProductionListIndexedDerivationCertificate rules 0 x x
  | step {n : Nat} {x y z : SententialForm terminal nonterminal}
      (stepCert : FiniteProductionListIndexedStepCertificate rules) :
      stepCert.Matches x y ->
      FiniteProductionListIndexedDerivationCertificate rules n y z ->
      FiniteProductionListIndexedDerivationCertificate rules (n + 1) x z

inductive FiniteProductionListIndexedDerivationCertificateData
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    Nat -> SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Type where
  | zero (x : SententialForm terminal nonterminal) :
      FiniteProductionListIndexedDerivationCertificateData rules 0 x x
  | step {n : Nat} {x y z : SententialForm terminal nonterminal}
      (stepCert : FiniteProductionListIndexedStepCertificate rules) :
      FiniteProductionListIndexedDerivationCertificateData rules n y z ->
      FiniteProductionListIndexedDerivationCertificateData
        rules (n + 1) x z

namespace FiniteProductionListIndexedDerivationCertificateData

def check [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)} :
    {n : Nat} -> {x y : SententialForm terminal nonterminal} ->
      FiniteProductionListIndexedDerivationCertificateData rules n x y ->
      Bool
  | 0, _, _, zero _ => true
  | _ + 1, x, _, step (y := mid) stepCert rest =>
      stepCert.check x mid && check rest

theorem to_indexedCertificate_of_check_eq_true
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    {cert :
      FiniteProductionListIndexedDerivationCertificateData rules n x y}
    (h : cert.check = true) :
    FiniteProductionListIndexedDerivationCertificate rules n x y := by
  induction cert with
  | zero x =>
      exact FiniteProductionListIndexedDerivationCertificate.zero x
  | step stepCert rest ih =>
      simp [check,
        FiniteProductionListIndexedStepCertificate.check_eq_true_iff]
        at h
      exact FiniteProductionListIndexedDerivationCertificate.step
        stepCert h.left (ih h.right)

theorem exists_check_eq_true_of_indexedCertificate
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (cert :
      FiniteProductionListIndexedDerivationCertificate rules n x y) :
    exists data :
      FiniteProductionListIndexedDerivationCertificateData rules n x y,
      data.check = true := by
  induction cert with
  | zero x =>
      exact ⟨zero x, rfl⟩
  | step stepCert hmatch _ ih =>
      rcases ih with ⟨rest, hrest⟩
      refine ⟨step stepCert rest, ?_⟩
      simp [check,
        FiniteProductionListIndexedStepCertificate.check_eq_true_iff,
        hmatch, hrest]

end FiniteProductionListIndexedDerivationCertificateData

def finiteProductionListCheckedIndexedDerivationCertificateSearch
    [DecidableEq terminal] [DecidableEq nonterminal]
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    (n : Nat) ->
      SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y =>
      listAny
        (fun candidate =>
          candidate.cert.check x candidate.mid &&
            finiteProductionListCheckedIndexedDerivationCertificateSearch
              rules n candidate.mid y)
        (finiteProductionListIndexedStepSearchCandidates rules x)

theorem finiteProductionListCheckedIndexedDerivationCertificateSearch_eq_true_of_data
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    {data :
      FiniteProductionListIndexedDerivationCertificateData rules n x y}
    (h : data.check = true) :
    finiteProductionListCheckedIndexedDerivationCertificateSearch
      rules n x y = true := by
  induction data with
  | zero x =>
      simp [finiteProductionListCheckedIndexedDerivationCertificateSearch]
  | step stepCert rest ih =>
      simp [FiniteProductionListIndexedDerivationCertificateData.check]
        at h
      rw [finiteProductionListCheckedIndexedDerivationCertificateSearch]
      apply (listAny_eq_true_iff _ _).mpr
      refine
        ⟨{ mid := _, cert := stepCert },
          finiteProductionListIndexedStepSearchCandidates_complete
            stepCert
            ((FiniteProductionListIndexedStepCertificate.check_eq_true_iff
              stepCert _ _).mp h.left),
          ?_⟩
      simp [h.left, ih h.right]

theorem finiteProductionListCheckedIndexedDerivationCertificateSearch_exists_data
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)} :
    forall {n : Nat} {x y : SententialForm terminal nonterminal},
      finiteProductionListCheckedIndexedDerivationCertificateSearch
        rules n x y = true ->
        exists data :
          FiniteProductionListIndexedDerivationCertificateData rules n x y,
          data.check = true
  | 0, x, y, h => by
      simp [finiteProductionListCheckedIndexedDerivationCertificateSearch]
        at h
      subst y
      exact ⟨FiniteProductionListIndexedDerivationCertificateData.zero x,
        rfl⟩
  | n + 1, x, y, h => by
      rw [finiteProductionListCheckedIndexedDerivationCertificateSearch] at h
      rcases (listAny_eq_true_iff _ _).mp h with
        ⟨candidate, _hmem, hcandidate⟩
      simp at hcandidate
      rcases
        finiteProductionListCheckedIndexedDerivationCertificateSearch_exists_data
          (rules := rules) hcandidate.right with
        ⟨rest, hrest⟩
      refine
        ⟨FiniteProductionListIndexedDerivationCertificateData.step
          candidate.cert rest, ?_⟩
      simp [FiniteProductionListIndexedDerivationCertificateData.check,
        hcandidate.left, hrest]

theorem finiteProductionListCheckedIndexedDerivationCertificateSearch_iff
    [DecidableEq terminal] [DecidableEq nonterminal]
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal} :
    finiteProductionListCheckedIndexedDerivationCertificateSearch
        rules n x y = true <->
      exists data :
        FiniteProductionListIndexedDerivationCertificateData rules n x y,
        data.check = true := by
  constructor
  · exact
      finiteProductionListCheckedIndexedDerivationCertificateSearch_exists_data
  · intro h
    rcases h with ⟨data, hdata⟩
    exact
      finiteProductionListCheckedIndexedDerivationCertificateSearch_eq_true_of_data
        hdata

theorem FiniteProductionListIndexedDerivationCertificate.to_certificate
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (cert :
      FiniteProductionListIndexedDerivationCertificate rules n x y) :
    FiniteProductionListDerivationCertificate rules n x y := by
  induction cert with
  | zero x =>
      exact FiniteProductionListDerivationCertificate.zero x
  | step stepCert hmatch _ ih =>
      exact FiniteProductionListDerivationCertificate.step
        (stepCert.to_stepCertificate hmatch) ih

theorem FiniteProductionListIndexedDerivationCertificate.of_certificate
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (cert :
      FiniteProductionListDerivationCertificate rules n x y) :
    FiniteProductionListIndexedDerivationCertificate rules n x y := by
  induction cert with
  | zero x =>
      exact FiniteProductionListIndexedDerivationCertificate.zero x
  | step hstep _ ih =>
      rcases
        FiniteProductionListIndexedStepCertificate.exists_of_stepCertificate
          hstep with
        ⟨stepCert, hmatch⟩
      exact FiniteProductionListIndexedDerivationCertificate.step
        stepCert hmatch ih

theorem finiteProductionListIndexedDerivationCertificate_iff_certificate
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal} :
    FiniteProductionListIndexedDerivationCertificate rules n x y <->
      FiniteProductionListDerivationCertificate rules n x y :=
  ⟨FiniteProductionListIndexedDerivationCertificate.to_certificate,
    FiniteProductionListIndexedDerivationCertificate.of_certificate⟩

theorem finiteProductionListIndexedDerivationCertificate_iff_derivesIn
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {n : Nat} {x y : SententialForm terminal nonterminal} :
    FiniteProductionListIndexedDerivationCertificate rules n x y <->
      GeneralGrammar.ProductionListDerivesIn rules n x y :=
  Iff.trans finiteProductionListIndexedDerivationCertificate_iff_certificate
    finiteProductionListDerivationCertificate_iff_derivesIn

def FiniteProductionListDerivationCertificateTrace
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  FiniteProductionListDerivationCertificate rules n
    [Symbol.nonterminal G.start]
    (SententialForm.terminalWord w)

def FiniteProductionListIndexedDerivationCertificateTrace
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  FiniteProductionListIndexedDerivationCertificate rules n
    [Symbol.nonterminal G.start]
    (SententialForm.terminalWord w)

def FiniteProductionListCheckedIndexedDerivationCertificateTrace
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) : Prop :=
  exists data :
    FiniteProductionListIndexedDerivationCertificateData rules n
      [Symbol.nonterminal G.start]
      (SententialForm.terminalWord w),
    data.check = true

theorem finiteProductionListCheckedIndexedDerivationCertificateSearch_iff_trace
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    finiteProductionListCheckedIndexedDerivationCertificateSearch
        rules n [Symbol.nonterminal G.start]
        (SententialForm.terminalWord w) = true <->
      FiniteProductionListCheckedIndexedDerivationCertificateTrace
        G rules w n := by
  simp [FiniteProductionListCheckedIndexedDerivationCertificateTrace,
    finiteProductionListCheckedIndexedDerivationCertificateSearch_iff]

instance finiteProductionListCheckedIndexedDerivationCertificateTraceDecidable
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (n : Nat) :
    Decidable
      (FiniteProductionListCheckedIndexedDerivationCertificateTrace
        G rules w n) := by
  by_cases h :
      finiteProductionListCheckedIndexedDerivationCertificateSearch
        rules n [Symbol.nonterminal G.start]
        (SententialForm.terminalWord w) = true
  · exact isTrue
      ((finiteProductionListCheckedIndexedDerivationCertificateSearch_iff_trace).mp
        h)
  · exact isFalse (by
      intro htrace
      exact h
        ((finiteProductionListCheckedIndexedDerivationCertificateSearch_iff_trace).mpr
          htrace))

theorem finiteProductionListDerivationCertificateTrace_iff_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListDerivationCertificateTrace G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  finiteProductionListDerivationCertificate_iff_derivesIn

theorem finiteProductionListIndexedDerivationCertificateTrace_iff_trace
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListIndexedDerivationCertificateTrace G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  finiteProductionListIndexedDerivationCertificate_iff_derivesIn

theorem finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_indexedTrace
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListCheckedIndexedDerivationCertificateTrace
        G rules w n <->
      FiniteProductionListIndexedDerivationCertificateTrace G rules w
        n := by
  constructor
  · intro h
    rcases h with ⟨data, hdata⟩
    exact
      FiniteProductionListIndexedDerivationCertificateData.to_indexedCertificate_of_check_eq_true
        hdata
  · intro h
    exact
      FiniteProductionListIndexedDerivationCertificateData.exists_check_eq_true_of_indexedCertificate
        h

theorem finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_trace
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {n : Nat} :
    FiniteProductionListCheckedIndexedDerivationCertificateTrace
        G rules w n <->
      FiniteProductionListDerivationTrace G rules w n :=
  Iff.trans
    finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_indexedTrace
    finiteProductionListIndexedDerivationCertificateTrace_iff_trace

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

def GeneralGrammarBoundedDerivationSearch
    (G : GeneralGrammar terminal nonterminal)
    (w : Word terminal) (limit : Nat) : Prop :=
  TraceHitsBy (GeneralGrammarDerivationTrace G) w limit

def FiniteProductionListBoundedDerivationSearch
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (limit : Nat) : Prop :=
  TraceHitsBy (FiniteProductionListDerivationTrace G rules) w limit

def FiniteProductionListBoundedCertificateSearch
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (limit : Nat) : Prop :=
  TraceHitsBy (FiniteProductionListDerivationCertificateTrace G rules)
    w limit

def FiniteProductionListBoundedIndexedCertificateSearch
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (limit : Nat) : Prop :=
  TraceHitsBy
    (FiniteProductionListIndexedDerivationCertificateTrace G rules)
    w limit

def FiniteProductionListBoundedCheckedIndexedCertificateSearch
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (limit : Nat) : Prop :=
  TraceHitsBy
    (FiniteProductionListCheckedIndexedDerivationCertificateTrace G rules)
    w limit

instance finiteProductionListBoundedCheckedIndexedCertificateSearchDecidable
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal))
    (w : Word terminal) (limit : Nat) :
    Decidable
      (FiniteProductionListBoundedCheckedIndexedCertificateSearch
        G rules w limit) := by
  unfold FiniteProductionListBoundedCheckedIndexedCertificateSearch
  infer_instance

theorem finiteProductionListBoundedCertificateSearch_iff_derivationSearch
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {limit : Nat} :
    FiniteProductionListBoundedCertificateSearch G rules w limit <->
      FiniteProductionListBoundedDerivationSearch G rules w limit := by
  constructor
  · intro h
    rcases h with ⟨n, hn, hcert⟩
    exact
      ⟨n, hn,
        (finiteProductionListDerivationCertificateTrace_iff_trace).mp
          hcert⟩
  · intro h
    rcases h with ⟨n, hn, htrace⟩
    exact
      ⟨n, hn,
        (finiteProductionListDerivationCertificateTrace_iff_trace).mpr
          htrace⟩

theorem finiteProductionListBoundedIndexedCertificateSearch_iff_derivationSearch
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {limit : Nat} :
    FiniteProductionListBoundedIndexedCertificateSearch G rules w limit <->
      FiniteProductionListBoundedDerivationSearch G rules w limit := by
  constructor
  · intro h
    rcases h with ⟨n, hn, hcert⟩
    exact
      ⟨n, hn,
        (finiteProductionListIndexedDerivationCertificateTrace_iff_trace).mp
          hcert⟩
  · intro h
    rcases h with ⟨n, hn, htrace⟩
    exact
      ⟨n, hn,
        (finiteProductionListIndexedDerivationCertificateTrace_iff_trace).mpr
          htrace⟩

theorem finiteProductionListBoundedCheckedIndexedCertificateSearch_iff_derivationSearch
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    {w : Word terminal} {limit : Nat} :
    FiniteProductionListBoundedCheckedIndexedCertificateSearch G rules
        w limit <->
      FiniteProductionListBoundedDerivationSearch G rules w limit := by
  constructor
  · intro h
    rcases h with ⟨n, hn, hcert⟩
    exact
      ⟨n, hn,
        (finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_trace).mp
          hcert⟩
  · intro h
    rcases h with ⟨n, hn, htrace⟩
    exact
      ⟨n, hn,
        (finiteProductionListCheckedIndexedDerivationCertificateTrace_iff_trace).mpr
          htrace⟩

theorem generalGrammarBoundedDerivationSearch_sound
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal} {limit : Nat}
    (hit : GeneralGrammarBoundedDerivationSearch G w limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  traceHitsBy_sound (generalGrammar_derivationTrace_acceptance G) hit

theorem generalGrammarBoundedDerivationSearch_complete
    {G : GeneralGrammar terminal nonterminal}
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat, GeneralGrammarBoundedDerivationSearch G w limit :=
  traceHitsBy_complete (generalGrammar_derivationTrace_acceptance G) hw

theorem finiteProductionListBoundedDerivationSearch_sound
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {limit : Nat}
    (hit : FiniteProductionListBoundedDerivationSearch G rules w limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  traceHitsBy_sound
    (finiteProductionListDerivationTrace_acceptance hrules) hit

theorem finiteProductionListBoundedDerivationSearch_complete
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat,
      FiniteProductionListBoundedDerivationSearch G rules w limit :=
  traceHitsBy_complete
    (finiteProductionListDerivationTrace_acceptance hrules) hw

theorem finiteProductionListBoundedCertificateSearch_sound
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {limit : Nat}
    (hit : FiniteProductionListBoundedCertificateSearch G rules w limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  finiteProductionListBoundedDerivationSearch_sound hrules
    ((finiteProductionListBoundedCertificateSearch_iff_derivationSearch).mp
      hit)

theorem finiteProductionListBoundedIndexedCertificateSearch_sound
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {limit : Nat}
    (hit :
      FiniteProductionListBoundedIndexedCertificateSearch G rules w
        limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  finiteProductionListBoundedDerivationSearch_sound hrules
    ((finiteProductionListBoundedIndexedCertificateSearch_iff_derivationSearch).mp
      hit)

theorem finiteProductionListBoundedCheckedIndexedCertificateSearch_sound
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal} {limit : Nat}
    (hit :
      FiniteProductionListBoundedCheckedIndexedCertificateSearch G rules w
        limit) :
    w ∈ GeneralGrammar.GeneratedLanguage G :=
  finiteProductionListBoundedDerivationSearch_sound hrules
    ((finiteProductionListBoundedCheckedIndexedCertificateSearch_iff_derivationSearch).mp
      hit)

theorem finiteProductionListBoundedCertificateSearch_complete
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat,
      FiniteProductionListBoundedCertificateSearch G rules w limit := by
  rcases finiteProductionListBoundedDerivationSearch_complete hrules hw with
    ⟨limit, hit⟩
  exact
    ⟨limit,
      (finiteProductionListBoundedCertificateSearch_iff_derivationSearch).mpr
        hit⟩

theorem finiteProductionListBoundedIndexedCertificateSearch_complete
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat,
      FiniteProductionListBoundedIndexedCertificateSearch G rules w
        limit := by
  rcases finiteProductionListBoundedDerivationSearch_complete hrules hw with
    ⟨limit, hit⟩
  exact
    ⟨limit,
      (finiteProductionListBoundedIndexedCertificateSearch_iff_derivationSearch).mpr
        hit⟩

theorem finiteProductionListBoundedCheckedIndexedCertificateSearch_complete
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs)
    {w : Word terminal}
    (hw : w ∈ GeneralGrammar.GeneratedLanguage G) :
    exists limit : Nat,
      FiniteProductionListBoundedCheckedIndexedCertificateSearch G rules w
        limit := by
  rcases finiteProductionListBoundedDerivationSearch_complete hrules hw with
    ⟨limit, hit⟩
  exact
    ⟨limit,
      (finiteProductionListBoundedCheckedIndexedCertificateSearch_iff_derivationSearch).mpr
        hit⟩

noncomputable def GeneralGrammarBoundedRecognizerProgram
    (G : GeneralGrammar terminal nonterminal) :
    StagedProgram terminal Unit :=
  by
    classical
    exact TraceRecognizerProgram (GeneralGrammarBoundedDerivationSearch G)

def FiniteProductionListCheckedIndexedCertificateRecognizerProgram
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  TraceRecognizerProgram
    (FiniteProductionListBoundedCheckedIndexedCertificateSearch G rules)

def FiniteProductionListCertificateRecognizerProgram
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListCheckedIndexedCertificateRecognizerProgram G rules

def FiniteProductionListIndexedCertificateRecognizerProgram
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListCheckedIndexedCertificateRecognizerProgram G rules

def FiniteProductionListBoundedRecognizerProgram
    [DecidableEq terminal] [DecidableEq nonterminal]
    (G : GeneralGrammar terminal nonterminal)
    (rules : List (GeneralGrammar.Production terminal nonterminal)) :
    StagedProgram terminal Unit :=
  FiniteProductionListCheckedIndexedCertificateRecognizerProgram G rules

theorem generalGrammarBoundedRecognizerProgram_acceptsLanguage
    (G : GeneralGrammar terminal nonterminal) :
    ProgramAcceptsLanguage
      (GeneralGrammarBoundedRecognizerProgram G)
      (GeneralGrammar.GeneratedLanguage G) := by
  classical
  apply traceRecognizerProgram_acceptsLanguage
  intro w
  constructor
  · intro h
    rcases h with ⟨limit, hit⟩
    exact generalGrammarBoundedDerivationSearch_sound hit
  · intro hw
    exact generalGrammarBoundedDerivationSearch_complete hw

theorem finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListCheckedIndexedCertificateRecognizerProgram G
        rules)
      (GeneralGrammar.GeneratedLanguage G) := by
  apply traceRecognizerProgram_acceptsLanguage
  intro w
  constructor
  · intro h
    rcases h with ⟨limit, hit⟩
    exact finiteProductionListBoundedCheckedIndexedCertificateSearch_sound
      hrules hit
  · intro hw
    exact finiteProductionListBoundedCheckedIndexedCertificateSearch_complete
      hrules hw

theorem finiteProductionListBoundedRecognizerProgram_acceptsLanguage
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListBoundedRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finiteProductionListCertificateRecognizerProgram_acceptsLanguage
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListCertificateRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finiteProductionListIndexedCertificateRecognizerProgram_acceptsLanguage
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    ProgramAcceptsLanguage
      (FiniteProductionListIndexedCertificateRecognizerProgram G rules)
      (GeneralGrammar.GeneratedLanguage G) :=
  finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
    hrules

theorem finiteProductionListCertificateRecognizerProgram_same_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (FiniteProductionListCertificateRecognizerProgram G rules) w [] <->
        ProgramHaltsWithOutput
          (FiniteProductionListBoundedRecognizerProgram G rules) w [] := by
  intro w
  exact Iff.trans
    ((finiteProductionListCertificateRecognizerProgram_acceptsLanguage
      hrules w))
    ((finiteProductionListBoundedRecognizerProgram_acceptsLanguage
      hrules w).symm)

theorem finiteProductionListIndexedCertificateRecognizerProgram_same_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (FiniteProductionListIndexedCertificateRecognizerProgram G rules)
          w [] <->
        ProgramHaltsWithOutput
          (FiniteProductionListBoundedRecognizerProgram G rules) w [] := by
  intro w
  exact Iff.trans
    ((finiteProductionListIndexedCertificateRecognizerProgram_acceptsLanguage
      hrules w))
    ((finiteProductionListBoundedRecognizerProgram_acceptsLanguage
      hrules w).symm)

theorem finiteProductionListCheckedIndexedCertificateRecognizerProgram_same_language
    [DecidableEq terminal] [DecidableEq nonterminal]
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (GeneralGrammar.Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <->
        GeneralGrammar.ProductionListProduces rules lhs rhs) :
    forall w : Word terminal,
      ProgramHaltsWithOutput
          (FiniteProductionListCheckedIndexedCertificateRecognizerProgram G
            rules)
          w [] <->
        ProgramHaltsWithOutput
          (FiniteProductionListBoundedRecognizerProgram G rules) w [] := by
  intro w
  exact Iff.trans
    ((finiteProductionListCheckedIndexedCertificateRecognizerProgram_acceptsLanguage
      hrules w))
    ((finiteProductionListBoundedRecognizerProgram_acceptsLanguage
      hrules w).symm)

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


end Computability
end FoC

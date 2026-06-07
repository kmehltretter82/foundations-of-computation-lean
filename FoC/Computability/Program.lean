import FoC.Computability.Enumerable

set_option doc.verso true

/-!
# Staged programs

## Program-level computability witnesses

This module records a lightweight program semantics for Chapter 5 arguments
that reason by finite stages.  A staged program may produce an output at a
given stage; absence of an output represents nontermination up to that stage.

The semantics is intentionally weaker than the concrete one-tape Turing-machine
layer.  It is strong enough to formalize bounded dovetailing over acceptance
traces and the equivalence between partial listings, unary partial ranges, and
partial-function programs without assuming a universal-machine interpreter.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: dovetailing paired recognizers and equivalent
  listing/range/program descriptions of recursively enumerable languages.
-/

namespace FoC
namespace Computability

open Languages

/-!
# Staged programs
-/

structure StagedProgram (input : Type u) (output : Type v) where
  run : Word input -> Nat -> Option (Word output)

def ProgramHaltsWithOutput
    (P : StagedProgram input output) (w : Word input)
    (out : Word output) : Prop :=
  exists n : Nat, P.run w n = some out

def ProgramAcceptsLanguage (P : StagedProgram input Unit)
    (L : Language input) : Prop :=
  forall w : Word input, ProgramHaltsWithOutput P w [] <-> w ∈ L

def ProgramAcceptable (L : Language input) : Prop :=
  exists P : StagedProgram input Unit, ProgramAcceptsLanguage P L

def ProgramBoolDecides (P : StagedProgram input Bool)
    (L : Language input) : Prop :=
  (forall w : Word input, ProgramHaltsWithOutput P w [true] <-> w ∈ L) ∧
    (forall w : Word input,
      ProgramHaltsWithOutput P w [false] <-> ¬ w ∈ L)

def ProgramBoolDecidable (L : Language input) : Prop :=
  exists P : StagedProgram input Bool, ProgramBoolDecides P L

def ProgramRangeLanguage (P : StagedProgram input output) :
    Language output :=
  fun out => exists w : Word input, exists n : Nat,
    P.run w n = some out

def ProgramAcceptorCompilationPrinciple (input : Type u) : Prop :=
  forall L : Language input, ProgramAcceptable L -> TuringAcceptable L

def ProgramBoolDeciderCompilationPrinciple (input : Type u) : Prop :=
  forall L : Language input, ProgramBoolDecidable L -> TuringDecidable L

/-!
# Acceptance traces and programs
-/

def ProgramAcceptanceTrace (P : StagedProgram input Unit)
    (w : Word input) (n : Nat) : Prop :=
  P.run w n = some []

theorem programAcceptsLanguage_acceptanceTrace
    {P : StagedProgram input Unit} {L : Language input}
    (h : ProgramAcceptsLanguage P L) :
    AcceptanceTrace (ProgramAcceptanceTrace P) L := by
  intro w
  constructor
  · intro hit
    exact (h w).mp hit
  · intro hw
    exact (h w).mpr hw

theorem programAcceptable_has_acceptanceTrace
    {L : Language input}
    (h : ProgramAcceptable L) :
    exists trace : Word input -> Nat -> Prop, AcceptanceTrace trace L := by
  cases h with
  | intro P hP =>
      exact Exists.intro (ProgramAcceptanceTrace P)
        (programAcceptsLanguage_acceptanceTrace hP)

noncomputable def TraceRecognizerProgram
    (trace : Word input -> Nat -> Prop) :
    StagedProgram input Unit :=
  by
    classical
    exact { run := fun w n => if trace w n then some [] else none }

theorem traceRecognizerProgram_run_of_trace
    {trace : Word input -> Nat -> Prop}
    {w : Word input} {n : Nat}
    (h : trace w n) :
    (TraceRecognizerProgram trace).run w n = some [] := by
  classical
  simp [TraceRecognizerProgram, h]
  rfl

theorem traceRecognizerProgram_acceptsLanguage
    {trace : Word input -> Nat -> Prop} {L : Language input}
    (h : AcceptanceTrace trace L) :
    ProgramAcceptsLanguage (TraceRecognizerProgram trace) L := by
  intro w
  constructor
  · intro hit
    cases hit with
    | intro n hn =>
        by_cases htrace : trace w n
        · exact (h w).mp (Exists.intro n htrace)
        · simp [TraceRecognizerProgram, htrace] at hn
  · intro hw
    cases (h w).mpr hw with
    | intro n hn =>
        exact Exists.intro n (traceRecognizerProgram_run_of_trace hn)

theorem acceptanceTrace_programAcceptable
    {trace : Word input -> Nat -> Prop} {L : Language input}
    (h : AcceptanceTrace trace L) :
    ProgramAcceptable L :=
  Exists.intro (TraceRecognizerProgram trace)
    (traceRecognizerProgram_acceptsLanguage h)

theorem programAcceptable_iff_has_acceptanceTrace
    (L : Language input) :
    ProgramAcceptable L <->
      exists trace : Word input -> Nat -> Prop, AcceptanceTrace trace L := by
  constructor
  · exact programAcceptable_has_acceptanceTrace
  · intro h
    cases h with
    | intro trace htrace =>
        exact acceptanceTrace_programAcceptable htrace

/-!
# Dovetailing complementary traces

At each stage, the dovetailing program asks whether either trace has hit by
that bound.  It returns the one-symbol true word for the language trace and
the one-symbol false word for the complement trace.  If both are available,
the accepting side is chosen; the complementary-trace invariant proves that
this tie case is impossible for a fixed language.
-/

noncomputable def DovetailProgram
    (accept reject : Word input -> Nat -> Prop) :
    StagedProgram input Bool :=
  by
    classical
    exact
      { run := fun w n =>
          if TraceHitsBy accept w n then some [true]
          else if TraceHitsBy reject w n then some [false]
          else none }

theorem dovetailProgram_run_accept_hit
    {accept reject : Word input -> Nat -> Prop}
    {w : Word input} {limit : Nat}
    (hit : TraceHitsBy accept w limit) :
    (DovetailProgram accept reject).run w limit = some [true] := by
  classical
  simp [DovetailProgram, hit]
  rfl

theorem dovetailProgram_run_reject_hit
    {accept reject : Word input -> Nat -> Prop}
    {w : Word input} {limit : Nat}
    (noAccept : ¬ TraceHitsBy accept w limit)
    (hit : TraceHitsBy reject w limit) :
    (DovetailProgram accept reject).run w limit = some [false] := by
  classical
  simp [DovetailProgram, noAccept, hit]
  rfl

theorem dovetailProgram_run_no_hit
    {accept reject : Word input -> Nat -> Prop}
    {w : Word input} {limit : Nat}
    (noAccept : ¬ TraceHitsBy accept w limit)
    (noReject : ¬ TraceHitsBy reject w limit) :
    (DovetailProgram accept reject).run w limit = none := by
  classical
  simp [DovetailProgram, noAccept, noReject]

theorem programAcceptsLanguage_of_equal
    {P : StagedProgram input Unit} {L K : Language input}
    (h : ProgramAcceptsLanguage P L) (hEq : Language.Equal L K) :
    ProgramAcceptsLanguage P K := by
  intro w
  exact Iff.trans (h w) (hEq w)

theorem programAcceptable_of_equal
    {L K : Language input}
    (h : ProgramAcceptable L) (hEq : Language.Equal L K) :
    ProgramAcceptable K := by
  cases h with
  | intro P hP =>
      exact Exists.intro P (programAcceptsLanguage_of_equal hP hEq)

theorem dovetailProgram_true_sound
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hh : ProgramHaltsWithOutput
      (DovetailProgram accept reject) w [true]) :
    w ∈ L := by
  classical
  cases hh with
  | intro limit hrun =>
      by_cases ha : TraceHitsBy accept w limit
      · exact complementaryTraceAcceptsBy_sound h ha
      · by_cases hr : TraceHitsBy reject w limit
        · have hrunFalse :
            (DovetailProgram accept reject).run w limit = some [false] :=
            dovetailProgram_run_reject_hit ha hr
          rw [hrunFalse] at hrun
          cases hrun
        · have hrunNone :
            (DovetailProgram accept reject).run w limit = none :=
            dovetailProgram_run_no_hit ha hr
          rw [hrunNone] at hrun
          cases hrun

theorem dovetailProgram_true_complete
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hw : w ∈ L) :
    ProgramHaltsWithOutput (DovetailProgram accept reject) w [true] := by
  cases complementaryTraceAcceptsBy_complete h hw with
  | intro limit hit =>
      exact Exists.intro limit (dovetailProgram_run_accept_hit hit)

theorem dovetailProgram_false_sound
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hh : ProgramHaltsWithOutput
      (DovetailProgram accept reject) w [false]) :
    ¬ w ∈ L := by
  classical
  cases hh with
  | intro limit hrun =>
      by_cases ha : TraceHitsBy accept w limit
      · have hrunTrue :
          (DovetailProgram accept reject).run w limit = some [true] :=
          dovetailProgram_run_accept_hit ha
        rw [hrunTrue] at hrun
        cases hrun
      · by_cases hr : TraceHitsBy reject w limit
        · exact complementaryTraceRejectsBy_sound h hr
        · have hrunNone :
            (DovetailProgram accept reject).run w limit = none :=
            dovetailProgram_run_no_hit ha hr
          rw [hrunNone] at hrun
          cases hrun

theorem dovetailProgram_false_complete
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hw : ¬ w ∈ L) :
    ProgramHaltsWithOutput (DovetailProgram accept reject) w [false] := by
  cases complementaryTraceRejectsBy_complete h hw with
  | intro limit hit =>
      have noAccept : ¬ TraceHitsBy accept w limit := by
        intro ha
        exact hw (complementaryTraceAcceptsBy_sound h ha)
      exact Exists.intro limit
        (dovetailProgram_run_reject_hit noAccept hit)

theorem dovetailProgram_decides
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L) :
    ProgramBoolDecides (DovetailProgram accept reject) L := by
  constructor
  · intro w
    constructor
    · exact dovetailProgram_true_sound h
    · exact dovetailProgram_true_complete h
  · intro w
    constructor
    · exact dovetailProgram_false_sound h
    · exact dovetailProgram_false_complete h

theorem reCoRe_has_dovetailProgram {L : Language input}
    (h : RecursivelyEnumerableWithComplement L) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L ∧
        ProgramBoolDecides (DovetailProgram accept reject) L := by
  cases recursivelyEnumerable_with_complement_has_complementaryTraces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          exact Exists.intro accept
            (Exists.intro reject
              (And.intro hreject (dovetailProgram_decides hreject)))

theorem reCoRe_programBoolDecidable {L : Language input}
    (h : RecursivelyEnumerableWithComplement L) :
    ProgramBoolDecidable L := by
  cases reCoRe_has_dovetailProgram h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          exact Exists.intro (DovetailProgram accept reject) hreject.right

theorem reCoReToDecidablePrinciple_of_programBoolCompiler
    (hcompile : ProgramBoolDeciderCompilationPrinciple input) :
    ReCoReToDecidablePrinciple input := by
  intro L h
  exact hcompile L (reCoRe_programBoolDecidable h)

theorem turingAcceptable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple input)
    {L : Language input}
    (h : ProgramAcceptable L) :
    TuringAcceptable L :=
  hcompile L h

theorem recursivelyEnumerable_of_programCompiler
    (hcompile : ProgramAcceptorCompilationPrinciple input)
    {L : Language input}
    (h : ProgramAcceptable L) :
    RecursivelyEnumerable L :=
  hcompile L h

/-!
# Partial listings, ranges, and programs
-/

def ListingProgram (output : Type u) : Type u :=
  Nat -> Option (Word output)

def ListingProgramLists (stream : ListingProgram output)
    (L : Language output) : Prop :=
  PartiallyListedBy stream L

def PartialUnaryRangeProgram (output : Type u) : Type u :=
  Word Unit -> Option (Word output)

def PartialUnaryRangeProgramGenerates
    (f : PartialUnaryRangeProgram output)
    (L : Language output) : Prop :=
  Language.Equal (PartialRangeLanguage f) L

def PartialFunctionProgram
    (f : Word input -> Option (Word output)) :
    StagedProgram input output where
  run w n := if n = 0 then f w else none

def PartialUnaryFunctionProgramRange (L : Language output) : Prop :=
  exists f : PartialUnaryRangeProgram output,
    Language.Equal (ProgramRangeLanguage (PartialFunctionProgram f)) L

theorem listingProgram_iff_partiallyListable
    (L : Language output) :
    (exists stream : ListingProgram output,
      ListingProgramLists stream L) <-> PartiallyListable L := by
  constructor
  · intro h
    cases h with
    | intro stream hstream =>
        exact Exists.intro stream hstream
  · intro h
    cases h with
    | intro stream hstream =>
        exact Exists.intro stream hstream

theorem partialUnaryRangeProgram_iff_partialRangeOfUnaryFunction
    (L : Language output) :
    (exists f : PartialUnaryRangeProgram output,
      PartialUnaryRangeProgramGenerates f L) <->
        PartialRangeOfUnaryFunction L := by
  constructor
  · intro h
    cases h with
    | intro f hf =>
        exact Exists.intro f hf
  · intro h
    cases h with
    | intro f hf =>
        exact Exists.intro f hf

theorem partialFunctionProgram_range
    (f : Word input -> Option (Word output)) :
    Language.Equal
      (ProgramRangeLanguage (PartialFunctionProgram f))
      (PartialRangeLanguage f) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro x hx =>
        cases hx with
        | intro n hn =>
            by_cases hz : n = 0
            · exists x
              simpa [PartialFunctionProgram, hz] using hn
            · simp [PartialFunctionProgram, hz] at hn
  · intro hw
    cases hw with
    | intro x hx =>
        exists x
        exists 0

theorem partialUnaryFunctionProgramRange_iff_partialRangeOfUnaryFunction
    (L : Language output) :
    PartialUnaryFunctionProgramRange L <->
      PartialRangeOfUnaryFunction L := by
  constructor
  · intro h
    cases h with
    | intro f hf =>
        exists f
        exact Language.equal_trans
          (Language.equal_symm (partialFunctionProgram_range f)) hf
  · intro h
    cases h with
    | intro f hf =>
        exists f
        exact Language.equal_trans (partialFunctionProgram_range f) hf

theorem partiallyListable_iff_partialUnaryFunctionProgramRange
    (L : Language output) :
    PartiallyListable L <-> PartialUnaryFunctionProgramRange L := by
  exact Iff.trans
    (partiallyListable_iff_partialRangeOfUnaryFunction L)
    (Iff.symm
      (partialUnaryFunctionProgramRange_iff_partialRangeOfUnaryFunction L))

end Computability
end FoC

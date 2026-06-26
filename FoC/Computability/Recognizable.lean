import FoC.Computability.Computable

set_option doc.verso true

/-!
# Recognizable and decidable languages

## Acceptance and decision

This module packages the Chapter 5 language predicates.  A language is
acceptable when some machine halts exactly on its members, and decidable when a
machine gives explicit yes/no outputs for every input.

## Book coordinates

Used by:
- Chapter 5, Section 5.1: decidable and acceptable languages.
- Chapter 5, Section 5.2: recursive and recursively enumerable language
  vocabulary.
- Chapter 5, Section 5.3: undecidability statements.
-/

namespace FoC
namespace Computability

open Languages

/-!
# Acceptance and decidability predicates

Acceptability is halting exactly on members. Decidability is halting with one
of two output symbols according to membership.
-/

def AcceptsLanguage (M : TuringMachine symbol state)
    (encodeInput : input -> symbol) (L : Language input) : Prop :=
  forall w : Word input,
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) <-> w ∈ L

def TuringAcceptable (L : Language input) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        AcceptsLanguage M encodeInput L

def DecidesLanguage (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (zero one : symbol)
    (L : Language input) : Prop :=
  forall w : Word input,
    (w ∈ L ->
      TuringMachine.HaltsWithOutput M (EncodeWord encodeInput w) [one]) ∧
    (¬ w ∈ L ->
      TuringMachine.HaltsWithOutput M (EncodeWord encodeInput w) [zero])

def DecidesLanguageByHeadOutput (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (zero one : symbol)
    (L : Language input) : Prop :=
  forall w : Word input,
    (w ∈ L ->
      exists final,
        TuringMachine.Computes M (TuringMachine.initial M
          (EncodeWord encodeInput w)) final ∧
          TuringMachine.Halted M final ∧
          Tape.read final.tape = some one) ∧
    (¬ w ∈ L ->
      exists final,
        TuringMachine.Computes M (TuringMachine.initial M
          (EncodeWord encodeInput w)) final ∧
          TuringMachine.Halted M final ∧
          Tape.read final.tape = some zero)

def StoppedDecidesLanguage (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (zero one : symbol)
    (L : Language input) : Prop :=
  TuringMachine.HaltingTransitionsDisabled M ∧
    zero ≠ one ∧ DecidesLanguage M encodeInput zero one L

def StoppedDecidesLanguageByHeadOutput (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (zero one : symbol)
    (L : Language input) : Prop :=
  TuringMachine.HaltingTransitionsDisabled M ∧
    zero ≠ one ∧ DecidesLanguageByHeadOutput M encodeInput zero one L

def TuringDecidable (L : Language input) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        exists zero : symbol, exists one : symbol,
          DecidesLanguage M encodeInput zero one L

def StoppedTuringDecidable (L : Language input) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        exists zero : symbol, exists one : symbol,
          StoppedDecidesLanguage M encodeInput zero one L

def StoppedTuringDecidableByHeadOutput (L : Language input) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        exists zero : symbol, exists one : symbol,
          StoppedDecidesLanguageByHeadOutput M encodeInput zero one L

def Recursive (L : Language input) : Prop :=
  TuringDecidable L

def RecursivelyEnumerable (L : Language input) : Prop :=
  TuringAcceptable L

def CoRecursivelyEnumerable (L : Language input) : Prop :=
  RecursivelyEnumerable (Language.Compl L)

def RecursivelyEnumerableWithComplement (L : Language input) : Prop :=
  RecursivelyEnumerable L ∧ CoRecursivelyEnumerable L

/-!
# Trace-search principles

The trace predicates abstract the dovetailing argument that searches accepting
and rejecting computations in parallel.
-/

def AcceptanceTrace (trace : Word input -> Nat -> Prop)
    (L : Language input) : Prop :=
  forall w : Word input, (exists n : Nat, trace w n) <-> w ∈ L

def ComplementaryAcceptanceTraces
    (accept reject : Word input -> Nat -> Prop)
    (L : Language input) : Prop :=
  AcceptanceTrace accept L ∧ AcceptanceTrace reject (Language.Compl L)

def TraceHitsBy (trace : Word input -> Nat -> Prop)
    (w : Word input) (limit : Nat) : Prop :=
  exists n : Nat, n ≤ limit ∧ trace w n

def ComplementaryTraceSearchHit
    (accept reject : Word input -> Nat -> Prop)
    (w : Word input) (limit : Nat) : Prop :=
  TraceHitsBy accept w limit ∨ TraceHitsBy reject w limit

/-!
# Characteristic functions

Decidability can be represented by a computable Boolean characteristic function
with explicit true and false outputs.
-/

noncomputable def CharacteristicFunction (L : Language input) :
    Word input -> Word Bool :=
  by
    classical
    exact fun w => if w ∈ L then [true] else [false]

def BoolCharacteristic (χ : Word input -> Word Bool)
    (L : Language input) : Prop :=
  forall w : Word input,
    (w ∈ L -> χ w = [true]) ∧ (¬ w ∈ L -> χ w = [false])

def HasComputableCharacteristic (L : Language input) : Prop :=
  exists χ : Word input -> Word Bool,
    TuringComputable χ ∧ BoolCharacteristic χ L

def AcceptsByOneOutput (M : TuringMachine symbol state)
    (encodeInput : input -> symbol) (one : symbol)
    (L : Language input) : Prop :=
  forall w : Word input,
    TuringMachine.HaltsWithOutput M (EncodeWord encodeInput w) [one] <->
      w ∈ L

def RejectsByZeroOutput (M : TuringMachine symbol state)
    (encodeInput : input -> symbol) (zero : symbol)
    (L : Language input) : Prop :=
  forall w : Word input,
    TuringMachine.HaltsWithOutput M (EncodeWord encodeInput w) [zero] <->
      ¬ w ∈ L

/-!
# Classical equivalence principles

These proposition-level principles state the standard relationships between
decidable, recursively enumerable, and co-recursively enumerable languages.
-/

def DecidableToAcceptablePrinciple (input : Type u) : Prop :=
  forall L : Language input, TuringDecidable L -> TuringAcceptable L

def ReCoReToDecidablePrinciple (input : Type u) : Prop :=
  forall L : Language input,
    RecursivelyEnumerableWithComplement L -> TuringDecidable L

def RecursiveIffReCoRePrinciple (input : Type u) : Prop :=
  forall L : Language input,
    Recursive L <-> RecursivelyEnumerableWithComplement L

/-!
# Extensionality and accepted languages

The first theorem group transports recognizability and acceptability across
language equality and the machine-level accepted-language predicate.
-/

theorem acceptsLanguage_of_equal {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {L K : Language input}
    (h : AcceptsLanguage M encodeInput L)
    (hEq : Language.Equal L K) :
    AcceptsLanguage M encodeInput K := by
  intro w
  exact Iff.trans (h w) (hEq w)

theorem turing_acceptable_of_equal {L K : Language input}
    (h : TuringAcceptable L) (hEq : Language.Equal L K) :
    TuringAcceptable K := by
  rcases h with ⟨symbol, state, M, encodeInput, hacc⟩
  exact ⟨symbol, state, M, encodeInput,
    acceptsLanguage_of_equal hacc hEq⟩

theorem turing_acceptable_of_recognizes {input : Type} {state : Type}
    {M : TuringMachine input state}
    {L : Language input}
    (h : TuringMachine.Recognizes M L) :
    TuringAcceptable L := by
  exists input
  exists state
  exists M
  exists fun a : input => a
  intro w
  rw [encodeWord_id]
  exact h w

theorem turing_acceptable_acceptedLanguage {input : Type} {state : Type}
    (M : TuringMachine input state) :
    TuringAcceptable (TuringMachine.AcceptedLanguage M) :=
  turing_acceptable_of_recognizes (TuringMachine.recognizes_acceptedLanguage M)

theorem characteristicFunction_is_boolCharacteristic
    (L : Language input) :
    BoolCharacteristic (CharacteristicFunction L) L := by
  classical
  intro w
  constructor
  · intro hw
    simp [CharacteristicFunction, hw]
  · intro hw
    simp [CharacteristicFunction, hw]

theorem boolCharacteristic_of_equal
    {χ : Word input -> Word Bool} {L K : Language input}
    (hχ : BoolCharacteristic χ L) (hEq : Language.Equal L K) :
    BoolCharacteristic χ K := by
  intro w
  constructor
  · intro hw
    exact (hχ w).left ((hEq w).mpr hw)
  · intro hw
    exact (hχ w).right (fun hL => hw ((hEq w).mp hL))

/-!
# Decidability implies computable characteristic

Given a decider, its yes/no outputs compute the Boolean characteristic function
of the language.
-/

theorem computesFunction_characteristicFunction
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L) :
    ComputesFunction M encodeInput
      (fun b : Bool => if b then one else zero)
      (CharacteristicFunction L) := by
  classical
  intro w
  by_cases hw : w ∈ L
  · simpa [CharacteristicFunction, hw, EncodeWord] using (h w).left hw
  · simpa [CharacteristicFunction, hw, EncodeWord] using (h w).right hw

theorem turingDecidable_characteristicFunction_turingComputable
    {L : Language input}
    (h : TuringDecidable L) :
    TuringComputable (CharacteristicFunction L) := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exact ⟨symbol, state, M, encodeInput,
    (fun b : Bool => if b then one else zero),
    computesFunction_characteristicFunction hdec⟩

theorem turingDecidable_has_computableCharacteristic
    {L : Language input}
    (h : TuringDecidable L) :
    HasComputableCharacteristic L :=
  Exists.intro (CharacteristicFunction L)
    (And.intro
      (turingDecidable_characteristicFunction_turingComputable h)
      (characteristicFunction_is_boolCharacteristic L))

theorem boolCharacteristic_turingDecidable
    {χ : Word input -> Word Bool} {L : Language input}
    (hcomp : TuringComputable χ) (hχ : BoolCharacteristic χ L) :
    TuringDecidable L := by
  rcases hcomp with ⟨symbol, state, M, encodeInput, encodeOutput, hcomputes⟩
  refine ⟨symbol, state, M, encodeInput,
    encodeOutput false, encodeOutput true, ?_⟩
  intro w
  constructor
  · intro hw
    have hχw : χ w = [true] := (hχ w).left hw
    have hhalt := hcomputes w
    rw [hχw] at hhalt
    simpa [EncodeWord] using hhalt
  · intro hw
    have hχw : χ w = [false] := (hχ w).right hw
    have hhalt := hcomputes w
    rw [hχw] at hhalt
    simpa [EncodeWord] using hhalt

theorem hasComputableCharacteristic_turingDecidable
    {L : Language input}
    (h : HasComputableCharacteristic L) :
    TuringDecidable L := by
  rcases h with ⟨χ, hcomp, hχ⟩
  exact boolCharacteristic_turingDecidable hcomp hχ

theorem turingDecidable_iff_hasComputableCharacteristic
    (L : Language input) :
    TuringDecidable L <-> HasComputableCharacteristic L := by
  constructor
  · exact turingDecidable_has_computableCharacteristic
  · exact hasComputableCharacteristic_turingDecidable

theorem computesPartialFunction_accepts_domain
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Option (Word output)}
    (h : ComputesPartialFunction M encodeInput encodeOutput f) :
    AcceptsLanguage M encodeInput (PartialFunctionDomain f) := by
  intro w
  exact computesPartialFunction_halts_iff_domain h w

theorem turingComputablePartial_domain_acceptable
    {f : Word input -> Option (Word output)}
    (h : TuringComputablePartial f) :
    TuringAcceptable (PartialFunctionDomain f) := by
  rcases h with ⟨symbol, state, M, encodeInput, _encodeOutput, hcomp⟩
  exact ⟨symbol, state, M, encodeInput,
    computesPartialFunction_accepts_domain hcomp⟩

theorem turingComputablePartial_domain_recursivelyEnumerable
    {f : Word input -> Option (Word output)}
    (h : TuringComputablePartial f) :
    RecursivelyEnumerable (PartialFunctionDomain f) :=
  turingComputablePartial_domain_acceptable h

theorem acceptanceTrace_sound {trace : Word input -> Nat -> Prop}
    {L : Language input}
    (h : AcceptanceTrace trace L) {w : Word input} {n : Nat}
    (hn : trace w n) :
    w ∈ L :=
  (h w).mp (Exists.intro n hn)

theorem acceptanceTrace_complete {trace : Word input -> Nat -> Prop}
    {L : Language input}
    (h : AcceptanceTrace trace L) {w : Word input}
    (hw : w ∈ L) :
    exists n : Nat, trace w n :=
  (h w).mpr hw

theorem traceHitsBy_of_trace {trace : Word input -> Nat -> Prop}
    {w : Word input} {n : Nat}
    (hn : trace w n) :
    TraceHitsBy trace w n :=
  Exists.intro n (And.intro (Nat.le_refl n) hn)

theorem traceHitsBy_mono {trace : Word input -> Nat -> Prop}
    {w : Word input} {m n : Nat}
    (hmn : m ≤ n)
    (h : TraceHitsBy trace w m) :
    TraceHitsBy trace w n := by
  rcases h with ⟨k, hkm, hk⟩
  exact ⟨k, Nat.le_trans hkm hmn, hk⟩

theorem traceHitsBy_sound {trace : Word input -> Nat -> Prop}
    {L : Language input}
    (h : AcceptanceTrace trace L)
    {w : Word input} {limit : Nat}
    (hit : TraceHitsBy trace w limit) :
    w ∈ L := by
  rcases hit with ⟨_n, _hle, hn⟩
  exact acceptanceTrace_sound h hn

theorem traceHitsBy_complete {trace : Word input -> Nat -> Prop}
    {L : Language input}
    (h : AcceptanceTrace trace L)
    {w : Word input}
    (hw : w ∈ L) :
    exists limit : Nat, TraceHitsBy trace w limit := by
  rcases acceptanceTrace_complete h hw with ⟨n, hn⟩
  exact ⟨n, traceHitsBy_of_trace hn⟩

theorem complementaryAcceptanceTraces_accept_sound
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input} {n : Nat}
    (hn : accept w n) :
    w ∈ L :=
  acceptanceTrace_sound h.left hn

theorem complementaryAcceptanceTraces_reject_sound
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input} {n : Nat}
    (hn : reject w n) :
    ¬ w ∈ L :=
  acceptanceTrace_sound h.right hn

theorem complementaryAcceptanceTraces_accept_complete
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hw : w ∈ L) :
    exists n : Nat, accept w n :=
  acceptanceTrace_complete h.left hw

theorem complementaryAcceptanceTraces_reject_complete
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hw : ¬ w ∈ L) :
    exists n : Nat, reject w n :=
  acceptanceTrace_complete h.right hw

theorem complementaryAcceptanceTraces_eventually_hits
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word input) :
    (w ∈ L -> exists n : Nat, accept w n) ∧
      (¬ w ∈ L -> exists n : Nat, reject w n) :=
  And.intro
    (fun hw => complementaryAcceptanceTraces_accept_complete h hw)
    (fun hw => complementaryAcceptanceTraces_reject_complete h hw)

theorem complementaryAcceptanceTraces_eventually_hits_classical
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word input) :
    exists n : Nat, accept w n ∨ reject w n := by
  classical
  by_cases hw : w ∈ L
  · cases complementaryAcceptanceTraces_accept_complete h hw with
    | intro n hn => exact Exists.intro n (Or.inl hn)
  · cases complementaryAcceptanceTraces_reject_complete h hw with
    | intro n hn => exact Exists.intro n (Or.inr hn)

theorem complementaryTraceAcceptsBy_sound
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input} {limit : Nat}
    (hit : TraceHitsBy accept w limit) :
    w ∈ L :=
  traceHitsBy_sound h.left hit

theorem complementaryTraceRejectsBy_sound
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input} {limit : Nat}
    (hit : TraceHitsBy reject w limit) :
    ¬ w ∈ L :=
  traceHitsBy_sound h.right hit

theorem complementaryTraceAcceptsBy_complete
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hw : w ∈ L) :
    exists limit : Nat, TraceHitsBy accept w limit :=
  traceHitsBy_complete h.left hw

theorem complementaryTraceRejectsBy_complete
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input}
    (hw : ¬ w ∈ L) :
    exists limit : Nat, TraceHitsBy reject w limit :=
  traceHitsBy_complete h.right hw

theorem complementaryTraceSearch_no_conflict
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    {w : Word input} {acceptLimit rejectLimit : Nat}
    (ha : TraceHitsBy accept w acceptLimit)
    (hr : TraceHitsBy reject w rejectLimit) :
    False :=
  complementaryTraceRejectsBy_sound h hr
    (complementaryTraceAcceptsBy_sound h ha)

theorem complementaryTraceSearch_eventually_hits_by
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word input) :
    exists limit : Nat, ComplementaryTraceSearchHit accept reject w limit := by
  cases complementaryAcceptanceTraces_eventually_hits_classical h w with
  | intro n hn =>
      exists n
      cases hn with
      | inl ha => exact Or.inl (traceHitsBy_of_trace ha)
      | inr hr => exact Or.inr (traceHitsBy_of_trace hr)

theorem complementaryTraceSearch_eventually_classifies
    {accept reject : Word input -> Nat -> Prop}
    {L : Language input}
    (h : ComplementaryAcceptanceTraces accept reject L)
    (w : Word input) :
    exists limit : Nat,
      (TraceHitsBy accept w limit ∧ w ∈ L) ∨
        (TraceHitsBy reject w limit ∧ ¬ w ∈ L) := by
  cases complementaryTraceSearch_eventually_hits_by h w with
  | intro limit hit =>
      exists limit
      cases hit with
      | inl ha =>
          exact Or.inl (And.intro ha (complementaryTraceAcceptsBy_sound h ha))
      | inr hr =>
          exact Or.inr (And.intro hr (complementaryTraceRejectsBy_sound h hr))

theorem acceptsLanguage_acceptanceTrace
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {L : Language input}
    (h : AcceptsLanguage M encodeInput L) :
    AcceptanceTrace
      (fun w n => TuringMachine.HaltsOnInputIn M n (EncodeWord encodeInput w))
      L := by
  intro w
  exact Iff.trans
    (TuringMachine.halts_on_input_iff_exists_halts_on_input_in
      M (EncodeWord encodeInput w)).symm
    (h w)

theorem turing_acceptable_has_acceptanceTrace {L : Language input}
    (h : TuringAcceptable L) :
    exists trace : Word input -> Nat -> Prop, AcceptanceTrace trace L := by
  rcases h with ⟨_symbol, _state, M, encodeInput, hacc⟩
  exact ⟨fun w n =>
    TuringMachine.HaltsOnInputIn M n (EncodeWord encodeInput w),
    acceptsLanguage_acceptanceTrace hacc⟩

theorem recursivelyEnumerable_has_acceptanceTrace {L : Language input}
    (h : RecursivelyEnumerable L) :
    exists trace : Word input -> Nat -> Prop, AcceptanceTrace trace L :=
  turing_acceptable_has_acceptanceTrace h

theorem turing_acceptable_with_complement_has_complementaryTraces
    {L : Language input}
    (hL : TuringAcceptable L)
    (hCompl : TuringAcceptable (Language.Compl L)) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L := by
  rcases turing_acceptable_has_acceptanceTrace hL with ⟨accept, haccept⟩
  rcases turing_acceptable_has_acceptanceTrace hCompl with ⟨reject, hreject⟩
  exact ⟨accept, reject, haccept, hreject⟩

theorem recursivelyEnumerable_with_complement_has_complementaryTraces
    {L : Language input}
    (h : RecursivelyEnumerableWithComplement L) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L :=
  turing_acceptable_with_complement_has_complementaryTraces h.left h.right

theorem decidesLanguage_of_equal {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L K : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (hEq : Language.Equal L K) :
    DecidesLanguage M encodeInput zero one K := by
  intro w
  constructor
  · intro hw
    exact (h w).left ((hEq w).mpr hw)
  · intro hw
    apply (h w).right
    intro hL
    exact hw ((hEq w).mp hL)

theorem stoppedDecidesLanguage_decides {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    DecidesLanguage M encodeInput zero one L :=
  h.right.right

theorem stoppedTuringDecidable_to_turingDecidable {L : Language input}
    (h : StoppedTuringDecidable L) :
    TuringDecidable L := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hstop⟩
  exact ⟨symbol, state, M, encodeInput, zero, one,
    stoppedDecidesLanguage_decides hstop⟩

theorem turing_decidable_of_equal {L K : Language input}
    (h : TuringDecidable L) (hEq : Language.Equal L K) :
    TuringDecidable K := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exact ⟨symbol, state, M, encodeInput, zero, one,
    decidesLanguage_of_equal hdec hEq⟩

theorem decider_halts_on_all_inputs {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) := by
  by_cases hw : w ∈ L
  · exact TuringMachine.halts_with_output_implies_halts ((h w).left hw)
  · exact TuringMachine.halts_with_output_implies_halts ((h w).right hw)

theorem decider_halts_in_on_all_inputs {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    exists n : Nat,
      TuringMachine.HaltsOnInputIn M n (EncodeWord encodeInput w) :=
  (TuringMachine.halts_on_input_iff_exists_halts_on_input_in
    M (EncodeWord encodeInput w)).mp
    (decider_halts_on_all_inputs h w)

theorem decider_accepts_in_of_mem {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    exists n : Nat,
      TuringMachine.HaltsWithOutputIn
        M n (EncodeWord encodeInput w) [one] :=
  (TuringMachine.halts_with_output_iff_exists_halts_with_output_in
    M (EncodeWord encodeInput w) [one]).mp
    ((h w).left hw)

theorem decider_rejects_in_of_not_mem {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : ¬ w ∈ L) :
    exists n : Nat,
      TuringMachine.HaltsWithOutputIn
        M n (EncodeWord encodeInput w) [zero] :=
  (TuringMachine.halts_with_output_iff_exists_halts_with_output_in
    M (EncodeWord encodeInput w) [zero]).mp
    ((h w).right hw)

theorem decider_accept_output_sound_of_stopped
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hout : TuringMachine.HaltsWithOutput
      M (EncodeWord encodeInput w) [one]) :
    w ∈ L := by
  classical
  by_cases hw : w ∈ L
  · exact hw
  · exfalso
    have hzero := (h w).right hw
    have houtEq := TuringMachine.halts_with_output_unique hstop hout hzero
    have honeZero : one = zero := by
      cases houtEq
      rfl
    exact hzeroOne honeZero.symm

theorem decider_reject_output_sound_of_stopped
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hout : TuringMachine.HaltsWithOutput
      M (EncodeWord encodeInput w) [zero]) :
    ¬ w ∈ L := by
  intro hw
  have hone := (h w).left hw
  have houtEq := TuringMachine.halts_with_output_unique hstop hout hone
  have hzeroEqOne : zero = one := by
    cases houtEq
    rfl
  exact hzeroOne hzeroEqOne

theorem decider_accept_output_in_sound_of_stopped
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input} {n : Nat}
    (hout : TuringMachine.HaltsWithOutputIn
      M n (EncodeWord encodeInput w) [one]) :
    w ∈ L :=
  decider_accept_output_sound_of_stopped hstop hzeroOne h
    (TuringMachine.halts_with_output_in_to_halts_with_output hout)

theorem decider_reject_output_in_sound_of_stopped
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input} {n : Nat}
    (hout : TuringMachine.HaltsWithOutputIn
      M n (EncodeWord encodeInput w) [zero]) :
    ¬ w ∈ L :=
  decider_reject_output_sound_of_stopped hstop hzeroOne h
    (TuringMachine.halts_with_output_in_to_halts_with_output hout)

theorem stopped_decider_has_complementary_output_traces
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L) :
    ComplementaryAcceptanceTraces
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [one])
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [zero])
      L := by
  constructor
  · intro w
    constructor
    · intro hit
      cases hit with
      | intro n hn =>
          exact decider_accept_output_in_sound_of_stopped
            hstop hzeroOne h hn
    · intro hw
      exact decider_accepts_in_of_mem h hw
  · intro w
    constructor
    · intro hit
      cases hit with
      | intro n hn =>
          exact decider_reject_output_in_sound_of_stopped
            hstop hzeroOne h hn
    · intro hw
      exact decider_rejects_in_of_not_mem h hw

theorem stopped_decider_acceptanceTrace
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L) :
    AcceptanceTrace
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [one])
      L :=
  (stopped_decider_has_complementary_output_traces hstop hzeroOne h).left

theorem stopped_decider_complement_acceptanceTrace
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L) :
    AcceptanceTrace
      (fun w n =>
        TuringMachine.HaltsWithOutputIn
          M n (EncodeWord encodeInput w) [zero])
      (Language.Compl L) :=
  (stopped_decider_has_complementary_output_traces hstop hzeroOne h).right

theorem stoppedTuringDecidable_has_complementary_output_traces
    {L : Language input}
    (h : StoppedTuringDecidable L) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L := by
  rcases h with ⟨_symbol, _state, M, encodeInput, zero, one, hstopped⟩
  exact
    ⟨fun w n => TuringMachine.HaltsWithOutputIn
        M n (EncodeWord encodeInput w) [one],
      fun w n => TuringMachine.HaltsWithOutputIn
        M n (EncodeWord encodeInput w) [zero],
      stopped_decider_has_complementary_output_traces
        hstopped.left hstopped.right.left hstopped.right.right⟩

theorem stoppedTuringDecidable_has_acceptanceTrace
    {L : Language input}
    (h : StoppedTuringDecidable L) :
    exists trace : Word input -> Nat -> Prop,
      AcceptanceTrace trace L := by
  rcases stoppedTuringDecidable_has_complementary_output_traces h with
    ⟨accept, _reject, htraces⟩
  exact ⟨accept, htraces.left⟩

theorem stoppedTuringDecidable_complement_has_acceptanceTrace
    {L : Language input}
    (h : StoppedTuringDecidable L) :
    exists trace : Word input -> Nat -> Prop,
      AcceptanceTrace trace (Language.Compl L) := by
  rcases stoppedTuringDecidable_has_complementary_output_traces h with
    ⟨_accept, reject, htraces⟩
  exact ⟨reject, htraces.right⟩

theorem stoppedDecidesLanguage_acceptsByOneOutput
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    AcceptsByOneOutput M encodeInput one L := by
  intro w
  constructor
  · intro hout
    exact decider_accept_output_sound_of_stopped h.left h.right.left
      h.right.right hout
  · intro hw
    exact (h.right.right w).left hw

theorem stoppedDecidesLanguage_rejectsByZeroOutput
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    RejectsByZeroOutput M encodeInput zero L := by
  intro w
  constructor
  · intro hout
    exact decider_reject_output_sound_of_stopped h.left h.right.left
      h.right.right hout
  · intro hw
    exact (h.right.right w).right hw

theorem stoppedTuringDecidable_has_output_classifiers
    {L : Language input}
    (h : StoppedTuringDecidable L) :
    exists symbol : Type, exists state : Type,
      exists M : TuringMachine symbol state,
        exists encodeInput : input -> symbol,
          exists zero : symbol, exists one : symbol,
            AcceptsByOneOutput M encodeInput one L ∧
              RejectsByZeroOutput M encodeInput zero L := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hstopped⟩
  exact ⟨symbol, state, M, encodeInput, zero, one,
    stoppedDecidesLanguage_acceptsByOneOutput hstopped,
    stoppedDecidesLanguage_rejectsByZeroOutput hstopped⟩

theorem stoppedTuringDecidable_bounded_search_eventually_classifies
    {L : Language input}
    (h : StoppedTuringDecidable L)
    (w : Word input) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L ∧
        exists limit : Nat,
          (TraceHitsBy accept w limit ∧ w ∈ L) ∨
            (TraceHitsBy reject w limit ∧ ¬ w ∈ L) := by
  rcases stoppedTuringDecidable_has_complementary_output_traces h with
    ⟨accept, reject, htraces⟩
  exact ⟨accept, reject, htraces,
    complementaryTraceSearch_eventually_classifies htraces w⟩

theorem decides_complement {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L) :
    DecidesLanguage M encodeInput one zero (Language.Compl L) := by
  classical
  intro w
  constructor
  · intro hw
    exact (h w).right hw
  · intro hw
    have hL : w ∈ L := by
      apply Classical.byContradiction
      intro hnot
      exact hw hnot
    exact (h w).left hL

theorem stoppedDecidesLanguage_complement {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    StoppedDecidesLanguage M encodeInput one zero (Language.Compl L) := by
  constructor
  · exact h.left
  constructor
  · intro honeZero
    exact h.right.left honeZero.symm
  · exact decides_complement h.right.right

theorem turing_decidable_has_total_halting_decider {L : Language input}
    (h : TuringDecidable L) :
    exists symbol : Type, exists state : Type,
      exists M : TuringMachine symbol state,
        exists encodeInput : input -> symbol,
          forall w : Word input,
            TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) := by
  rcases h with ⟨symbol, state, M, encodeInput, _zero, _one, hdec⟩
  exact ⟨symbol, state, M, encodeInput,
    fun w => decider_halts_on_all_inputs hdec w⟩

theorem turing_decidable_complement {L : Language input}
    (h : TuringDecidable L) : TuringDecidable (Language.Compl L) := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hdec⟩
  exact ⟨symbol, state, M, encodeInput, one, zero,
    decides_complement hdec⟩

theorem stoppedTuringDecidable_complement {L : Language input}
    (h : StoppedTuringDecidable L) :
    StoppedTuringDecidable (Language.Compl L) := by
  rcases h with ⟨symbol, state, M, encodeInput, zero, one, hstopped⟩
  exact ⟨symbol, state, M, encodeInput, one, zero,
    stoppedDecidesLanguage_complement hstopped⟩

theorem turing_decidable_of_complement {L : Language input}
    (h : TuringDecidable (Language.Compl L)) : TuringDecidable L :=
  turing_decidable_of_equal (turing_decidable_complement h) (Language.double_compl L)

theorem turing_decidable_complement_iff {L : Language input} :
    TuringDecidable (Language.Compl L) <-> TuringDecidable L := by
  constructor
  · exact turing_decidable_of_complement
  · exact turing_decidable_complement

theorem recursive_complement {L : Language input}
    (h : Recursive L) : Recursive (Language.Compl L) :=
  turing_decidable_complement h

theorem recursive_of_complement {L : Language input}
    (h : Recursive (Language.Compl L)) : Recursive L :=
  turing_decidable_of_complement h

theorem recursive_complement_iff {L : Language input} :
    Recursive (Language.Compl L) <-> Recursive L :=
  turing_decidable_complement_iff

theorem recursive_reCoRe_of_decidableToAcceptable
    (haccept : DecidableToAcceptablePrinciple input)
    {L : Language input}
    (h : Recursive L) :
    RecursivelyEnumerableWithComplement L := by
  constructor
  · exact haccept L h
  · exact haccept (Language.Compl L) (turing_decidable_complement h)

theorem recursive_iff_reCoRe_of_principles
    (haccept : DecidableToAcceptablePrinciple input)
    (hdovetail : ReCoReToDecidablePrinciple input)
    (L : Language input) :
    Recursive L <-> RecursivelyEnumerableWithComplement L := by
  constructor
  · exact recursive_reCoRe_of_decidableToAcceptable haccept
  · intro h
    exact hdovetail L h

theorem recursiveIffReCoRePrinciple_of_principles
    (haccept : DecidableToAcceptablePrinciple input)
    (hdovetail : ReCoReToDecidablePrinciple input) :
    RecursiveIffReCoRePrinciple input :=
  recursive_iff_reCoRe_of_principles haccept hdovetail

theorem recursive_of_equal {L K : Language input}
    (h : Recursive L) (hEq : Language.Equal L K) :
    Recursive K :=
  turing_decidable_of_equal h hEq

theorem recursivelyEnumerable_of_equal {L K : Language input}
    (h : RecursivelyEnumerable L) (hEq : Language.Equal L K) :
    RecursivelyEnumerable K :=
  turing_acceptable_of_equal h hEq

end Computability
end FoC

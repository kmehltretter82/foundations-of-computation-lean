import FoC.Computability.Computable

namespace FoC
namespace Computability

/-!
Turing-decidable and Turing-acceptable languages.

Used by:
- Chapter 5, Section 5.1: decidable and acceptable languages.
- Chapter 5, Section 5.2: recursive and recursively enumerable language
  vocabulary.
- Chapter 5, Section 5.3: undecidability statements.
-/

open Languages

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

def StoppedDecidesLanguage (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (zero one : symbol)
    (L : Language input) : Prop :=
  TuringMachine.HaltingTransitionsDisabled M ∧
    zero ≠ one ∧ DecidesLanguage M encodeInput zero one L

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

def Recursive (L : Language input) : Prop :=
  TuringDecidable L

def RecursivelyEnumerable (L : Language input) : Prop :=
  TuringAcceptable L

def CoRecursivelyEnumerable (L : Language input) : Prop :=
  RecursivelyEnumerable (Language.Compl L)

def RecursivelyEnumerableWithComplement (L : Language input) : Prop :=
  RecursivelyEnumerable L ∧ CoRecursivelyEnumerable L

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
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput hacc =>
                  exists symbol
                  exists state
                  exists M
                  exists encodeInput
                  exact acceptsLanguage_of_equal hacc hEq

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
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro encodeOutput hcomp =>
                      exists symbol
                      exists state
                      exists M
                      exists encodeInput
                      exact computesPartialFunction_accepts_domain hcomp

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
  cases h with
  | intro k hk =>
      exists k
      exact And.intro (Nat.le_trans hk.left hmn) hk.right

theorem traceHitsBy_sound {trace : Word input -> Nat -> Prop}
    {L : Language input}
    (h : AcceptanceTrace trace L)
    {w : Word input} {limit : Nat}
    (hit : TraceHitsBy trace w limit) :
    w ∈ L := by
  cases hit with
  | intro n hn =>
      exact acceptanceTrace_sound h hn.right

theorem traceHitsBy_complete {trace : Word input -> Nat -> Prop}
    {L : Language input}
    (h : AcceptanceTrace trace L)
    {w : Word input}
    (hw : w ∈ L) :
    exists limit : Nat, TraceHitsBy trace w limit := by
  cases acceptanceTrace_complete h hw with
  | intro n hn =>
      exact Exists.intro n (traceHitsBy_of_trace hn)

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
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput hacc =>
                  exists fun w n =>
                    TuringMachine.HaltsOnInputIn M n (EncodeWord encodeInput w)
                  exact acceptsLanguage_acceptanceTrace hacc

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
  cases turing_acceptable_has_acceptanceTrace hL with
  | intro accept haccept =>
      cases turing_acceptable_has_acceptanceTrace hCompl with
      | intro reject hreject =>
          exact Exists.intro accept
            (Exists.intro reject (And.intro haccept hreject))

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
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro zero hzero =>
                      cases hzero with
                      | intro one hstop =>
                          exact ⟨symbol, state, M, encodeInput, zero, one,
                            stoppedDecidesLanguage_decides hstop⟩

theorem turing_decidable_of_equal {L K : Language input}
    (h : TuringDecidable L) (hEq : Language.Equal L K) :
    TuringDecidable K := by
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro zero hzero =>
                      cases hzero with
                      | intro one hdec =>
                          exists symbol
                          exists state
                          exists M
                          exists encodeInput
                          exists zero
                          exists one
                          exact decidesLanguage_of_equal hdec hEq

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

theorem stoppedTuringDecidable_has_complementary_output_traces
    {L : Language input}
    (h : StoppedTuringDecidable L) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L := by
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro zero hzero =>
                      cases hzero with
                      | intro one hstopped =>
                          exists fun w n =>
                            TuringMachine.HaltsWithOutputIn
                              M n (EncodeWord encodeInput w) [one]
                          exists fun w n =>
                            TuringMachine.HaltsWithOutputIn
                              M n (EncodeWord encodeInput w) [zero]
                          exact stopped_decider_has_complementary_output_traces
                            hstopped.left hstopped.right.left
                            hstopped.right.right

theorem stoppedTuringDecidable_bounded_search_eventually_classifies
    {L : Language input}
    (h : StoppedTuringDecidable L)
    (w : Word input) :
    exists accept reject : Word input -> Nat -> Prop,
      ComplementaryAcceptanceTraces accept reject L ∧
        exists limit : Nat,
          (TraceHitsBy accept w limit ∧ w ∈ L) ∨
            (TraceHitsBy reject w limit ∧ ¬ w ∈ L) := by
  cases stoppedTuringDecidable_has_complementary_output_traces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject hreject =>
          exists accept
          exists reject
          constructor
          · exact hreject
          · exact complementaryTraceSearch_eventually_classifies hreject w

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
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro zero hzero =>
                      cases hzero with
                      | intro one hone =>
                          exists symbol
                          exists state
                          exists M
                          exists encodeInput
                          intro w
                          exact decider_halts_on_all_inputs hone w

theorem turing_decidable_complement {L : Language input}
    (h : TuringDecidable L) : TuringDecidable (Language.Compl L) := by
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro zero hzero =>
                      cases hzero with
                      | intro one hone =>
                          exists symbol
                          exists state
                          exists M
                          exists encodeInput
                          exists one
                          exists zero
                          exact decides_complement hone

theorem stoppedTuringDecidable_complement {L : Language input}
    (h : StoppedTuringDecidable L) :
    StoppedTuringDecidable (Language.Compl L) := by
  cases h with
  | intro symbol hsymbol =>
      cases hsymbol with
      | intro state hstate =>
          cases hstate with
          | intro M hM =>
              cases hM with
              | intro encodeInput henc =>
                  cases henc with
                  | intro zero hzero =>
                      cases hzero with
                      | intro one hstopped =>
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

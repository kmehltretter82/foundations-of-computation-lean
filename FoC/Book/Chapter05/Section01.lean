import FoC.Computability.Recognizable

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section01

/-!
# Chapter 5, Section 5.1: Turing Machines

This section introduces deterministic one-tape Turing machines, finite
computations, halting, accepted languages, computable string functions, and
decidable languages. The reusable machine and computability APIs are in
{module}`FoC.Computability.Tape`, {module}`FoC.Computability.TuringMachine`,
{module}`FoC.Computability.Computable`, and
{module}`FoC.Computability.Recognizable`.
-/

open Languages
open Computability

/-!
## Machines and Computations

The first definitions identify the book-facing vocabulary for moves, tapes,
machines, and halted configurations. The computation lemmas state determinism,
composition, exact-step computations, and uniqueness of halted results for
machines whose halting state has no outgoing transition.
-/

def MoveDirection := Direction

def MachineTape (symbol : Type u) := Tape symbol

theorem machine_tape_output_injective :
    Function.Injective (Tape.output : Word symbol -> Tape symbol) :=
  Tape.output_injective

def Machine (symbol : Type u) (state : Type v) :=
  TuringMachine symbol state

def MachineHaltingTransitionsDisabled (M : TuringMachine symbol state) : Prop :=
  TuringMachine.HaltingTransitionsDisabled M

theorem turing_step_is_computation {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Step M c d) :
    TuringMachine.Computes M c d :=
  TuringMachine.computes_of_step h

theorem turing_step_deterministic {M : TuringMachine symbol state}
    {c d e : TuringMachine.Configuration symbol state}
    (hcd : TuringMachine.Step M c d)
    (hce : TuringMachine.Step M c e) :
    d = e :=
  TuringMachine.step_deterministic hcd hce

theorem stopped_machine_has_no_step_from_halted
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {c d : TuringMachine.Configuration symbol state}
    (hhalt : TuringMachine.Halted M c)
    (hstep : TuringMachine.Step M c d) :
    False :=
  TuringMachine.no_step_from_halted hstop hhalt hstep

theorem turing_computation_transitive {M : TuringMachine symbol state}
    {a b c : TuringMachine.Configuration symbol state}
    (hab : TuringMachine.Computes M a b)
    (hbc : TuringMachine.Computes M b c) :
    TuringMachine.Computes M a c :=
  TuringMachine.computes_trans hab hbc

theorem turing_computation_in_steps_is_computation {M : TuringMachine symbol state}
    {n : Nat} {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.ComputesIn M n c d) :
    TuringMachine.Computes M c d :=
  TuringMachine.computesIn_to_computes h

theorem turing_computation_has_step_count {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Computes M c d) :
    exists n : Nat, TuringMachine.ComputesIn M n c d :=
  TuringMachine.computes_to_computesIn h

theorem turing_computation_in_steps_transitive {M : TuringMachine symbol state}
    {m n : Nat} {a b c : TuringMachine.Configuration symbol state}
    (hab : TuringMachine.ComputesIn M m a b)
    (hbc : TuringMachine.ComputesIn M n b c) :
    TuringMachine.ComputesIn M (m + n) a c :=
  TuringMachine.computesIn_trans hab hbc

theorem turing_computation_in_steps_deterministic
    {M : TuringMachine symbol state}
    {n : Nat} {c d e : TuringMachine.Configuration symbol state}
    (hcd : TuringMachine.ComputesIn M n c d)
    (hce : TuringMachine.ComputesIn M n c e) :
    d = e :=
  TuringMachine.computesIn_deterministic hcd hce

theorem stopped_machine_computation_from_halted_eq
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {c d : TuringMachine.Configuration symbol state}
    (hhalt : TuringMachine.Halted M c)
    (hcomp : TuringMachine.Computes M c d) :
    c = d :=
  TuringMachine.computes_from_halted_eq hstop hhalt hcomp

theorem stopped_machine_halted_final_unique
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {c d e : TuringMachine.Configuration symbol state}
    (hcd : TuringMachine.Computes M c d)
    (hd : TuringMachine.Halted M d)
    (hce : TuringMachine.Computes M c e)
    (he : TuringMachine.Halted M e) :
    d = e :=
  TuringMachine.computes_to_halted_unique hstop hcd hd hce he

/-!
## Halting and Output

Halting with output refines ordinary halting. The exact-step and stopped-machine
lemmas ensure that deterministic machines have unique outputs when they halt.
-/

theorem halts_with_output_implies_halts {M : TuringMachine symbol state}
    {w out : Word symbol} (h : TuringMachine.HaltsWithOutput M w out) :
    TuringMachine.HaltsOnInput M w :=
  TuringMachine.halts_with_output_implies_halts h

theorem halts_with_output_in_steps_implies_halts_in_steps
    {M : TuringMachine symbol state}
    {n : Nat} {w out : Word symbol}
    (h : TuringMachine.HaltsWithOutputIn M n w out) :
    TuringMachine.HaltsOnInputIn M n w :=
  TuringMachine.halts_with_output_in_implies_halts_in h

theorem halted_configuration_halts {M : TuringMachine symbol state}
    {c : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Halted M c) :
    TuringMachine.HaltsFrom M c :=
  TuringMachine.halts_from_halted h

theorem computation_to_halted_configuration_halts {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (hcomp : TuringMachine.Computes M c d)
    (hhalt : TuringMachine.Halted M d) :
    TuringMachine.HaltsFrom M c :=
  TuringMachine.halts_from_of_computes hcomp hhalt

theorem halting_iff_halting_in_some_steps
    (M : TuringMachine symbol state) (w : Word symbol) :
    TuringMachine.HaltsOnInput M w <->
      exists n : Nat, TuringMachine.HaltsOnInputIn M n w :=
  TuringMachine.halts_on_input_iff_exists_halts_on_input_in M w

theorem halting_with_output_iff_halting_with_output_in_some_steps
    (M : TuringMachine symbol state) (w out : Word symbol) :
    TuringMachine.HaltsWithOutput M w out <->
      exists n : Nat, TuringMachine.HaltsWithOutputIn M n w out :=
  TuringMachine.halts_with_output_iff_exists_halts_with_output_in M w out

theorem halting_with_output_in_steps_unique
    {M : TuringMachine symbol state}
    {n : Nat} {w out1 out2 : Word symbol}
    (h1 : TuringMachine.HaltsWithOutputIn M n w out1)
    (h2 : TuringMachine.HaltsWithOutputIn M n w out2) :
    out1 = out2 :=
  TuringMachine.halts_with_output_in_output_unique h1 h2

theorem stopped_machine_halting_output_unique
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {w out1 out2 : Word symbol}
    (h1 : TuringMachine.HaltsWithOutput M w out1)
    (h2 : TuringMachine.HaltsWithOutput M w out2) :
    out1 = out2 :=
  TuringMachine.halts_with_output_unique hstop h1 h2

theorem halting_after_previous_computation {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (hcomp : TuringMachine.Computes M c d)
    (hhalt : TuringMachine.HaltsFrom M d) :
    TuringMachine.HaltsFrom M c :=
  TuringMachine.halts_from_of_computes_prefix hcomp hhalt

/-!
## Recognizable and Computable Languages

Accepted languages are Turing-acceptable, and partial computable functions
halt exactly on their domains. These statements connect machines, languages,
and partial string functions.
-/

theorem machine_recognizes_accepted_language (M : TuringMachine symbol state) :
    TuringMachine.Recognizes M (TuringMachine.AcceptedLanguage M) :=
  TuringMachine.recognizes_acceptedLanguage M

theorem recognized_language_is_turing_acceptable
    {input : Type} {state : Type}
    {M : TuringMachine input state} {L : Language input}
    (h : TuringMachine.Recognizes M L) :
    TuringAcceptable L :=
  Computability.turing_acceptable_of_recognizes h

theorem accepted_language_is_turing_acceptable {input : Type} {state : Type}
    (M : TuringMachine input state) :
    TuringAcceptable (TuringMachine.AcceptedLanguage M) :=
  Computability.turing_acceptable_acceptedLanguage M

def TuringComputableFunction (f : Word input -> Word output) : Prop :=
  TuringComputable f

def TuringComputablePartialFunction
    (f : Word input -> Option (Word output)) : Prop :=
  TuringComputablePartial f

def TotalFunctionAsPartial (f : Word input -> Word output) :
    Word input -> Option (Word output) :=
  TotalAsPartial f

def PartialFunctionDomainLanguage
    (f : Word input -> Option (Word output)) : Language input :=
  PartialFunctionDomain f

theorem computable_function_as_partial
    {f : Word input -> Word output}
    (h : TuringComputableFunction f) :
    TuringComputablePartialFunction (TotalFunctionAsPartial f) :=
  Computability.turingComputable_to_partial h

theorem total_function_as_partial_domain_is_universal
    (f : Word input -> Word output) :
    Language.Equal
      (PartialFunctionDomainLanguage (TotalFunctionAsPartial f))
      (Language.Universal : Language input) :=
  Computability.totalAsPartial_domain_universal f

theorem partial_computable_function_halting_iff_domain
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Option (Word output)}
    (h : ComputesPartialFunction M encodeInput encodeOutput f)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) <->
      w ∈ PartialFunctionDomainLanguage f :=
  Computability.computesPartialFunction_halts_iff_domain h w

theorem partial_computable_function_of_pointwise_equal
    {f g : Word input -> Option (Word output)}
    (h : TuringComputablePartialFunction f)
    (hfg : forall w, f w = g w) :
    TuringComputablePartialFunction g :=
  Computability.turingComputablePartial_of_pointwise_equal h hfg

theorem partial_computable_function_domain_is_turing_acceptable
    {f : Word input -> Option (Word output)}
    (h : TuringComputablePartialFunction f) :
    TuringAcceptable (PartialFunctionDomainLanguage f) :=
  Computability.turingComputablePartial_domain_acceptable h

/-!
## Deciders and Characteristic Functions

The last group formalizes decidable languages through computable Boolean
characteristic functions and stopped 0/1 deciders. Complement and extensional
transport theorems give the basic closure properties used in Section 5.2.
-/

def TuringDecidableLanguage (L : Language input) : Prop :=
  TuringDecidable L

def TuringAcceptableLanguage (L : Language input) : Prop :=
  TuringAcceptable L

noncomputable def LanguageCharacteristicFunction (L : Language input) :
    Word input -> Word Bool :=
  CharacteristicFunction L

def LanguageBoolCharacteristic (χ : Word input -> Word Bool)
    (L : Language input) : Prop :=
  BoolCharacteristic χ L

def LanguageHasComputableCharacteristic (L : Language input) : Prop :=
  HasComputableCharacteristic L

def MachineAcceptsByOneOutput (M : TuringMachine symbol state)
    (encodeInput : input -> symbol) (one : symbol)
    (L : Language input) : Prop :=
  AcceptsByOneOutput M encodeInput one L

def MachineRejectsByZeroOutput (M : TuringMachine symbol state)
    (encodeInput : input -> symbol) (zero : symbol)
    (L : Language input) : Prop :=
  RejectsByZeroOutput M encodeInput zero L

theorem language_characteristic_function_is_bool_characteristic
    (L : Language input) :
    LanguageBoolCharacteristic (LanguageCharacteristicFunction L) L :=
  Computability.characteristicFunction_is_boolCharacteristic L

theorem decider_computes_language_characteristic_function
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L) :
    ComputesFunction M encodeInput
      (fun b : Bool => if b then one else zero)
      (LanguageCharacteristicFunction L) :=
  Computability.computesFunction_characteristicFunction h

theorem decidable_language_has_computable_characteristic
    {L : Language input}
    (h : TuringDecidableLanguage L) :
    LanguageHasComputableCharacteristic L :=
  Computability.turingDecidable_has_computableCharacteristic h

theorem computable_characteristic_decidable_language
    {L : Language input}
    (h : LanguageHasComputableCharacteristic L) :
    TuringDecidableLanguage L :=
  Computability.hasComputableCharacteristic_turingDecidable h

theorem decidable_language_iff_has_computable_characteristic
    (L : Language input) :
    TuringDecidableLanguage L <-> LanguageHasComputableCharacteristic L :=
  Computability.turingDecidable_iff_hasComputableCharacteristic L

theorem decider_halts_on_all_inputs {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) :=
  Computability.decider_halts_on_all_inputs h w

theorem decider_halts_in_some_steps_on_all_inputs
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    exists n : Nat,
      TuringMachine.HaltsOnInputIn M n (EncodeWord encodeInput w) :=
  Computability.decider_halts_in_on_all_inputs h w

theorem decider_accepts_in_some_steps_of_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : w ∈ L) :
    exists n : Nat,
      TuringMachine.HaltsWithOutputIn
        M n (EncodeWord encodeInput w) [one] :=
  Computability.decider_accepts_in_of_mem h hw

theorem decider_rejects_in_some_steps_of_not_mem
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hw : ¬ w ∈ L) :
    exists n : Nat,
      TuringMachine.HaltsWithOutputIn
        M n (EncodeWord encodeInput w) [zero] :=
  Computability.decider_rejects_in_of_not_mem h hw

theorem stopped_decider_accept_output_sound
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : MachineHaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hout : TuringMachine.HaltsWithOutput
      M (EncodeWord encodeInput w) [one]) :
    w ∈ L :=
  Computability.decider_accept_output_sound_of_stopped
    hstop hzeroOne h hout

theorem stopped_decider_reject_output_sound
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (hstop : MachineHaltingTransitionsDisabled M)
    (hzeroOne : zero ≠ one)
    (h : DecidesLanguage M encodeInput zero one L)
    {w : Word input}
    (hout : TuringMachine.HaltsWithOutput
      M (EncodeWord encodeInput w) [zero]) :
    ¬ w ∈ L :=
  Computability.decider_reject_output_sound_of_stopped
    hstop hzeroOne h hout

theorem stopped_decider_accepts_by_one_output
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    MachineAcceptsByOneOutput M encodeInput one L :=
  Computability.stoppedDecidesLanguage_acceptsByOneOutput h

theorem stopped_decider_rejects_by_zero_output
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    MachineRejectsByZeroOutput M encodeInput zero L :=
  Computability.stoppedDecidesLanguage_rejectsByZeroOutput h

theorem decider_for_complement {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L) :
    DecidesLanguage M encodeInput one zero (Language.Compl L) :=
  Computability.decides_complement h

theorem decidable_language_complement {L : Language input}
    (h : TuringDecidableLanguage L) :
    TuringDecidableLanguage (Language.Compl L) :=
  Computability.turing_decidable_complement h

theorem decidable_language_of_decidable_complement {L : Language input}
    (h : TuringDecidableLanguage (Language.Compl L)) :
    TuringDecidableLanguage L :=
  Computability.turing_decidable_of_complement h

theorem decidable_language_complement_iff {L : Language input} :
    TuringDecidableLanguage (Language.Compl L) <-> TuringDecidableLanguage L :=
  Computability.turing_decidable_complement_iff

theorem turing_acceptable_language_of_equal {L K : Language input}
    (h : TuringAcceptableLanguage L) (hEq : Language.Equal L K) :
    TuringAcceptableLanguage K :=
  Computability.turing_acceptable_of_equal h hEq

theorem turing_decidable_language_of_equal {L K : Language input}
    (h : TuringDecidableLanguage L) (hEq : Language.Equal L K) :
    TuringDecidableLanguage K :=
  Computability.turing_decidable_of_equal h hEq

end Section01
end Chapter05
end Book
end FoC

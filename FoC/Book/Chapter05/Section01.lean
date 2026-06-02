import FoC.Computability.Recognizable

namespace FoC
namespace Book
namespace Chapter05
namespace Section01

/-!
Book: Chapter 5, Section 5.1, Turing Machines.
-/

open Languages
open Computability

-- Book: Chapter 5, Section 5.1, moving a Turing-machine tape left or right.
def MoveDirection := Direction

-- Book: Chapter 5, Section 5.1, finite-window tape representation.
def MachineTape (symbol : Type u) := Tape symbol

-- Book: Chapter 5, Section 5.1, output tapes determine their output word.
theorem machine_tape_output_injective :
    Function.Injective (Tape.output : Word symbol -> Tape symbol) :=
  Tape.output_injective

-- Book: Chapter 5, Section 5.1, deterministic one-tape Turing machine.
def Machine (symbol : Type u) (state : Type v) :=
  TuringMachine symbol state

-- Book: Chapter 5, Section 5.1, the halting state has no outgoing
-- transition.
def MachineHaltingTransitionsDisabled (M : TuringMachine symbol state) : Prop :=
  TuringMachine.HaltingTransitionsDisabled M

-- Book: Chapter 5, Section 5.1, one computation step is a multi-step computation.
theorem turing_step_is_computation {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Step M c d) :
    TuringMachine.Computes M c d :=
  TuringMachine.computes_of_step h

-- Book: Chapter 5, Section 5.1, the next configuration is unique.
theorem turing_step_deterministic {M : TuringMachine symbol state}
    {c d e : TuringMachine.Configuration symbol state}
    (hcd : TuringMachine.Step M c d)
    (hce : TuringMachine.Step M c e) :
    d = e :=
  TuringMachine.step_deterministic hcd hce

-- Book: Chapter 5, Section 5.1, a stopped halting state has no next
-- configuration.
theorem stopped_machine_has_no_step_from_halted
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {c d : TuringMachine.Configuration symbol state}
    (hhalt : TuringMachine.Halted M c)
    (hstep : TuringMachine.Step M c d) :
    False :=
  TuringMachine.no_step_from_halted hstop hhalt hstep

-- Book: Chapter 5, Section 5.1, computations compose.
theorem turing_computation_transitive {M : TuringMachine symbol state}
    {a b c : TuringMachine.Configuration symbol state}
    (hab : TuringMachine.Computes M a b)
    (hbc : TuringMachine.Computes M b c) :
    TuringMachine.Computes M a c :=
  TuringMachine.computes_trans hab hbc

-- Book: Chapter 5, Section 5.1, a finite-step computation is a computation.
theorem turing_computation_in_steps_is_computation {M : TuringMachine symbol state}
    {n : Nat} {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.ComputesIn M n c d) :
    TuringMachine.Computes M c d :=
  TuringMachine.computesIn_to_computes h

-- Book: Chapter 5, Section 5.1, every finite computation has a step count.
theorem turing_computation_has_step_count {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Computes M c d) :
    exists n : Nat, TuringMachine.ComputesIn M n c d :=
  TuringMachine.computes_to_computesIn h

-- Book: Chapter 5, Section 5.1, exact-step computations compose with added
-- step counts.
theorem turing_computation_in_steps_transitive {M : TuringMachine symbol state}
    {m n : Nat} {a b c : TuringMachine.Configuration symbol state}
    (hab : TuringMachine.ComputesIn M m a b)
    (hbc : TuringMachine.ComputesIn M n b c) :
    TuringMachine.ComputesIn M (m + n) a c :=
  TuringMachine.computesIn_trans hab hbc

-- Book: Chapter 5, Section 5.1, a deterministic machine has at most one
-- configuration after a fixed number of steps.
theorem turing_computation_in_steps_deterministic
    {M : TuringMachine symbol state}
    {n : Nat} {c d e : TuringMachine.Configuration symbol state}
    (hcd : TuringMachine.ComputesIn M n c d)
    (hce : TuringMachine.ComputesIn M n c e) :
    d = e :=
  TuringMachine.computesIn_deterministic hcd hce

-- Book: Chapter 5, Section 5.1, a stopped halted configuration cannot move
-- along a computation.
theorem stopped_machine_computation_from_halted_eq
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {c d : TuringMachine.Configuration symbol state}
    (hhalt : TuringMachine.Halted M c)
    (hcomp : TuringMachine.Computes M c d) :
    c = d :=
  TuringMachine.computes_from_halted_eq hstop hhalt hcomp

-- Book: Chapter 5, Section 5.1, halted final configurations are unique for a
-- stopped deterministic machine.
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

-- Book: Chapter 5, Section 5.1, halting with output implies halting.
theorem halts_with_output_implies_halts {M : TuringMachine symbol state}
    {w out : Word symbol} (h : TuringMachine.HaltsWithOutput M w out) :
    TuringMachine.HaltsOnInput M w :=
  TuringMachine.halts_with_output_implies_halts h

-- Book: Chapter 5, Section 5.1, halting with output in n steps implies
-- halting in n steps.
theorem halts_with_output_in_steps_implies_halts_in_steps
    {M : TuringMachine symbol state}
    {n : Nat} {w out : Word symbol}
    (h : TuringMachine.HaltsWithOutputIn M n w out) :
    TuringMachine.HaltsOnInputIn M n w :=
  TuringMachine.halts_with_output_in_implies_halts_in h

-- Book: Chapter 5, Section 5.1, a halted configuration halts immediately.
theorem halted_configuration_halts {M : TuringMachine symbol state}
    {c : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Halted M c) :
    TuringMachine.HaltsFrom M c :=
  TuringMachine.halts_from_halted h

-- Book: Chapter 5, Section 5.1, a computation to a halted configuration halts.
theorem computation_to_halted_configuration_halts {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (hcomp : TuringMachine.Computes M c d)
    (hhalt : TuringMachine.Halted M d) :
    TuringMachine.HaltsFrom M c :=
  TuringMachine.halts_from_of_computes hcomp hhalt

-- Book: Chapter 5, Section 5.1, halting is equivalent to halting after
-- some finite number of steps.
theorem halting_iff_halting_in_some_steps
    (M : TuringMachine symbol state) (w : Word symbol) :
    TuringMachine.HaltsOnInput M w <->
      exists n : Nat, TuringMachine.HaltsOnInputIn M n w :=
  TuringMachine.halts_on_input_iff_exists_halts_on_input_in M w

-- Book: Chapter 5, Section 5.1, halting with output is equivalent to
-- halting with that output after some finite number of steps.
theorem halting_with_output_iff_halting_with_output_in_some_steps
    (M : TuringMachine symbol state) (w out : Word symbol) :
    TuringMachine.HaltsWithOutput M w out <->
      exists n : Nat, TuringMachine.HaltsWithOutputIn M n w out :=
  TuringMachine.halts_with_output_iff_exists_halts_with_output_in M w out

-- Book: Chapter 5, Section 5.1, a deterministic machine has at most one
-- output at a fixed halting time.
theorem halting_with_output_in_steps_unique
    {M : TuringMachine symbol state}
    {n : Nat} {w out1 out2 : Word symbol}
    (h1 : TuringMachine.HaltsWithOutputIn M n w out1)
    (h2 : TuringMachine.HaltsWithOutputIn M n w out2) :
    out1 = out2 :=
  TuringMachine.halts_with_output_in_output_unique h1 h2

-- Book: Chapter 5, Section 5.1, a stopped deterministic machine has at most
-- one halting output.
theorem stopped_machine_halting_output_unique
    {M : TuringMachine symbol state}
    (hstop : MachineHaltingTransitionsDisabled M)
    {w out1 out2 : Word symbol}
    (h1 : TuringMachine.HaltsWithOutput M w out1)
    (h2 : TuringMachine.HaltsWithOutput M w out2) :
    out1 = out2 :=
  TuringMachine.halts_with_output_unique hstop h1 h2

-- Book: Chapter 5, Section 5.1, halting is closed under adding previous
-- computation steps.
theorem halting_after_previous_computation {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (hcomp : TuringMachine.Computes M c d)
    (hhalt : TuringMachine.HaltsFrom M d) :
    TuringMachine.HaltsFrom M c :=
  TuringMachine.halts_from_of_computes_prefix hcomp hhalt

-- Book: Chapter 5, Section 5.1, the accepted language is recognized by its machine.
theorem machine_recognizes_accepted_language (M : TuringMachine symbol state) :
    TuringMachine.Recognizes M (TuringMachine.AcceptedLanguage M) :=
  TuringMachine.recognizes_acceptedLanguage M

-- Book: Chapter 5, Section 5.1, a direct machine recognizer gives a
-- Turing-acceptable language.
theorem recognized_language_is_turing_acceptable
    {input : Type} {state : Type}
    {M : TuringMachine input state} {L : Language input}
    (h : TuringMachine.Recognizes M L) :
    TuringAcceptable L :=
  Computability.turing_acceptable_of_recognizes h

-- Book: Chapter 5, Section 5.1, every machine's accepted language is
-- Turing-acceptable.
theorem accepted_language_is_turing_acceptable {input : Type} {state : Type}
    (M : TuringMachine input state) :
    TuringAcceptable (TuringMachine.AcceptedLanguage M) :=
  Computability.turing_acceptable_acceptedLanguage M

-- Book: Chapter 5, Section 5.1, Turing-computable string functions.
def TuringComputableFunction (f : Word input -> Word output) : Prop :=
  TuringComputable f

-- Book: Chapter 5, Section 5.1, Turing-computable partial string functions.
def TuringComputablePartialFunction
    (f : Word input -> Option (Word output)) : Prop :=
  TuringComputablePartial f

-- Book: Chapter 5, Section 5.1, a total string function viewed as a partial
-- function defined everywhere.
def TotalFunctionAsPartial (f : Word input -> Word output) :
    Word input -> Option (Word output) :=
  TotalAsPartial f

-- Book: Chapter 5, Section 5.1, the domain language of a partial string
-- function.
def PartialFunctionDomainLanguage
    (f : Word input -> Option (Word output)) : Language input :=
  PartialFunctionDomain f

-- Book: Chapter 5, Section 5.1, total computability gives partial
-- computability for the everywhere-defined partial function.
theorem computable_function_as_partial
    {f : Word input -> Word output}
    (h : TuringComputableFunction f) :
    TuringComputablePartialFunction (TotalFunctionAsPartial f) :=
  Computability.turingComputable_to_partial h

-- Book: Chapter 5, Section 5.1, the domain of a total function viewed as a
-- partial function is the universal language.
theorem total_function_as_partial_domain_is_universal
    (f : Word input -> Word output) :
    Language.Equal
      (PartialFunctionDomainLanguage (TotalFunctionAsPartial f))
      (Language.Universal : Language input) :=
  Computability.totalAsPartial_domain_universal f

-- Book: Chapter 5, Section 5.1, a machine computing a partial function halts
-- exactly on the function's domain.
theorem partial_computable_function_halting_iff_domain
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Option (Word output)}
    (h : ComputesPartialFunction M encodeInput encodeOutput f)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) <->
      w ∈ PartialFunctionDomainLanguage f :=
  Computability.computesPartialFunction_halts_iff_domain h w

-- Book: Chapter 5, Section 5.1, pointwise equal partial functions preserve
-- Turing computability.
theorem partial_computable_function_of_pointwise_equal
    {f g : Word input -> Option (Word output)}
    (h : TuringComputablePartialFunction f)
    (hfg : forall w, f w = g w) :
    TuringComputablePartialFunction g :=
  Computability.turingComputablePartial_of_pointwise_equal h hfg

-- Book: Chapter 5, Section 5.1, the domain of a Turing-computable partial
-- function is Turing-acceptable.
theorem partial_computable_function_domain_is_turing_acceptable
    {f : Word input -> Option (Word output)}
    (h : TuringComputablePartialFunction f) :
    TuringAcceptable (PartialFunctionDomainLanguage f) :=
  Computability.turingComputablePartial_domain_acceptable h

-- Book: Chapter 5, Section 5.1, decidable languages.
def TuringDecidableLanguage (L : Language input) : Prop :=
  TuringDecidable L

-- Book: Chapter 5, Section 5.1, acceptable languages.
def TuringAcceptableLanguage (L : Language input) : Prop :=
  TuringAcceptable L

-- Book: Chapter 5, Section 5.1, a decider halts on every input.
theorem decider_halts_on_all_inputs {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) :=
  Computability.decider_halts_on_all_inputs h w

-- Book: Chapter 5, Section 5.1, a decider has a finite halting time on every
-- input.
theorem decider_halts_in_some_steps_on_all_inputs
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    exists n : Nat,
      TuringMachine.HaltsOnInputIn M n (EncodeWord encodeInput w) :=
  Computability.decider_halts_in_on_all_inputs h w

-- Book: Chapter 5, Section 5.1, accepting decider outputs happen at a finite
-- stage.
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

-- Book: Chapter 5, Section 5.1, rejecting decider outputs happen at a finite
-- stage.
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

-- Book: Chapter 5, Section 5.1, for a stopped decider with distinct 0/1
-- symbols, output 1 is sound for membership.
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

-- Book: Chapter 5, Section 5.1, for a stopped decider with distinct 0/1
-- symbols, output 0 is sound for nonmembership.
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

-- Book: Chapter 5, Section 5.1, complementing a 0/1 decider swaps outputs.
theorem decider_for_complement {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L) :
    DecidesLanguage M encodeInput one zero (Language.Compl L) :=
  Computability.decides_complement h

-- Book: Chapter 5, Section 5.1, decidable languages are closed under complement.
theorem decidable_language_complement {L : Language input}
    (h : TuringDecidableLanguage L) :
    TuringDecidableLanguage (Language.Compl L) :=
  Computability.turing_decidable_complement h

-- Book: Chapter 5, Section 5.1, if the complement is decidable, then so is
-- the original language.
theorem decidable_language_of_decidable_complement {L : Language input}
    (h : TuringDecidableLanguage (Language.Compl L)) :
    TuringDecidableLanguage L :=
  Computability.turing_decidable_of_complement h

-- Book: Chapter 5, Section 5.1, decidability is equivalent for a language and
-- its complement.
theorem decidable_language_complement_iff {L : Language input} :
    TuringDecidableLanguage (Language.Compl L) <-> TuringDecidableLanguage L :=
  Computability.turing_decidable_complement_iff

-- Book: Chapter 5, Section 5.1, Turing-acceptability is extensional in the
-- accepted language.
theorem turing_acceptable_language_of_equal {L K : Language input}
    (h : TuringAcceptableLanguage L) (hEq : Language.Equal L K) :
    TuringAcceptableLanguage K :=
  Computability.turing_acceptable_of_equal h hEq

-- Book: Chapter 5, Section 5.1, Turing-decidability is extensional in the
-- decided language.
theorem turing_decidable_language_of_equal {L K : Language input}
    (h : TuringDecidableLanguage L) (hEq : Language.Equal L K) :
    TuringDecidableLanguage K :=
  Computability.turing_decidable_of_equal h hEq

end Section01
end Chapter05
end Book
end FoC

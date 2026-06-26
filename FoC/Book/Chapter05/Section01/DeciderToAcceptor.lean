import FoC.Book.Chapter05.Section01.Basic
import FoC.Computability.Transform

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section01

open Languages
open Computability

/-!
The next theorems are the concrete transition-level construction behind the
standard statement that a yes/no decider recognizes its yes-language. The
transformed machine simulates the stopped decider. If the simulated halted
head already reads the accepting symbol, it accepts immediately; otherwise it
uses the rejecting symbol as a temporary marker and alternately expands a
finite search window to the right and left until it finds the accepting symbol.

The head-output construction that follows is kept as the simpler local special
case where the halted head cell itself carries the accepting or rejecting
symbol.
-/

def NormalizedDeciderToAcceptorMachineState (state : Type u) :=
  NormalizedDeciderToAcceptorState state

noncomputable def NormalizedDeciderToAcceptorMachine
    (M : TuringMachine symbol state) (zero one : symbol) :
    TuringMachine symbol (NormalizedDeciderToAcceptorMachineState state) :=
  TuringMachine.normalizedDeciderToAcceptor M zero one

theorem normalized_output_scanner_complete
    (M : TuringMachine symbol state) {zero one : symbol}
    (hzeroOne : zero ≠ one) :
    TuringMachine.NormalizedOutputScannerComplete M zero one :=
  TuringMachine.normalizedOutputScannerComplete M hzeroOne

theorem stopped_normalized_decider_to_acceptor_accepts_language
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    AcceptsLanguage
      (NormalizedDeciderToAcceptorMachine M zero one) encodeInput L :=
  TuringMachine.normalizedDeciderToAcceptor_acceptsLanguage_of_stopped_decider h

theorem stopped_normalized_decider_language_is_turing_acceptable
    {symbol state input : Type}
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguage M encodeInput zero one L) :
    TuringAcceptableLanguage L :=
  TuringMachine.stoppedDecidesLanguage_to_turingAcceptable h

theorem stopped_normalized_decidable_language_is_turing_acceptable
    {input : Type} {L : Language input}
    (h : StoppedTuringDecidable L) :
    TuringAcceptableLanguage L :=
  TuringMachine.stoppedTuringDecidable_to_turingAcceptable h

def DeciderToAcceptorMachineState (state : Type u) :=
  DeciderToAcceptorState state

noncomputable def DeciderToAcceptorMachine
    (M : TuringMachine symbol state) (one : symbol) :
    TuringMachine symbol (DeciderToAcceptorMachineState state) :=
  TuringMachine.deciderToAcceptor M one

theorem stopped_decider_to_acceptor_accepts_language
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguageByHeadOutput M encodeInput zero one L) :
    AcceptsLanguage (DeciderToAcceptorMachine M one) encodeInput L :=
  TuringMachine.deciderToAcceptor_acceptsLanguage_of_stopped_decider
    h.left h.right.left h.right.right

theorem stopped_decider_language_is_turing_acceptable
    {symbol state input : Type}
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : StoppedDecidesLanguageByHeadOutput M encodeInput zero one L) :
    TuringAcceptableLanguage L :=
  TuringMachine.stoppedDecidesLanguageByHeadOutput_to_turingAcceptable h

theorem stopped_decidable_language_is_turing_acceptable
    {input : Type} {L : Language input}
    (h : StoppedTuringDecidableByHeadOutput L) :
    TuringAcceptableLanguage L :=
  TuringMachine.stoppedTuringDecidableByHeadOutput_to_turingAcceptable h


end Section01
end Chapter05
end Book
end FoC

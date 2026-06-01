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

-- Book: Chapter 5, Section 5.1, deterministic one-tape Turing machine.
def Machine (symbol : Type u) (state : Type v) :=
  TuringMachine symbol state

-- Book: Chapter 5, Section 5.1, one computation step is a multi-step computation.
theorem turing_step_is_computation {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    (h : TuringMachine.Step M c d) :
    TuringMachine.Computes M c d :=
  TuringMachine.computes_of_step h

-- Book: Chapter 5, Section 5.1, computations compose.
theorem turing_computation_transitive {M : TuringMachine symbol state}
    {a b c : TuringMachine.Configuration symbol state}
    (hab : TuringMachine.Computes M a b)
    (hbc : TuringMachine.Computes M b c) :
    TuringMachine.Computes M a c :=
  TuringMachine.computes_trans hab hbc

-- Book: Chapter 5, Section 5.1, halting with output implies halting.
theorem halts_with_output_implies_halts {M : TuringMachine symbol state}
    {w out : Word symbol} (h : TuringMachine.HaltsWithOutput M w out) :
    TuringMachine.HaltsOnInput M w :=
  TuringMachine.halts_with_output_implies_halts h

-- Book: Chapter 5, Section 5.1, Turing-computable string functions.
def TuringComputableFunction (f : Word input -> Word output) : Prop :=
  TuringComputable f

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

end Section01
end Chapter05
end Book
end FoC

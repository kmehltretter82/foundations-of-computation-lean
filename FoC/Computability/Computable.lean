import FoC.Computability.TuringMachine

namespace FoC
namespace Computability

/-!
Turing-computable functions.

Used by:
- Chapter 5, Section 5.1: Turing-computable string functions.
- Chapter 5, Section 5.2: recursively enumerable languages as ranges of
  computable functions.
-/

open Languages

def EncodeWord (encode : alpha -> symbol) (w : Word alpha) : Word symbol :=
  w.map encode

def ComputesFunction (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (encodeOutput : output -> symbol)
    (f : Word input -> Word output) : Prop :=
  forall w : Word input,
    TuringMachine.HaltsWithOutput M
      (EncodeWord encodeInput w)
      (EncodeWord encodeOutput (f w))

def TuringComputable (f : Word input -> Word output) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        exists encodeOutput : output -> symbol,
          ComputesFunction M encodeInput encodeOutput f

def ComputesPartialFunction (M : TuringMachine symbol state)
    (encodeInput : input -> symbol)
    (encodeOutput : output -> symbol)
    (f : Word input -> Option (Word output)) : Prop :=
  forall w : Word input,
    match f w with
    | some out =>
        TuringMachine.HaltsWithOutput M
          (EncodeWord encodeInput w)
          (EncodeWord encodeOutput out)
    | none =>
        ¬ TuringMachine.HaltsOnInput M (EncodeWord encodeInput w)

def TuringComputablePartial (f : Word input -> Option (Word output)) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        exists encodeOutput : output -> symbol,
          ComputesPartialFunction M encodeInput encodeOutput f

theorem computes_function_halts {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Word output}
    (h : ComputesFunction M encodeInput encodeOutput f) (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) :=
  TuringMachine.halts_with_output_implies_halts (h w)

end Computability
end FoC

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

theorem encodeWord_empty (encode : alpha -> symbol) :
    EncodeWord encode ([] : Word alpha) = [] :=
  rfl

theorem encodeWord_cons (encode : alpha -> symbol) (a : alpha)
    (w : Word alpha) :
    EncodeWord encode (a :: w) = encode a :: EncodeWord encode w :=
  rfl

theorem encodeWord_append (encode : alpha -> symbol)
    (x y : Word alpha) :
    EncodeWord encode (Word.Concat x y) =
      Word.Concat (EncodeWord encode x) (EncodeWord encode y) := by
  simp [EncodeWord, Word.Concat]

theorem encodeWord_id (w : Word alpha) :
    EncodeWord (fun a : alpha => a) w = w := by
  induction w with
  | nil => rfl
  | cons a rest ih =>
      rw [encodeWord_cons, ih]

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

theorem computesFunction_of_pointwise_equal {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f g : Word input -> Word output}
    (h : ComputesFunction M encodeInput encodeOutput f)
    (hfg : forall w, f w = g w) :
    ComputesFunction M encodeInput encodeOutput g := by
  intro w
  rw [← hfg w]
  exact h w

theorem turingComputable_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : TuringComputable f) (hfg : forall w, f w = g w) :
    TuringComputable g := by
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
                      exists encodeOutput
                      exact computesFunction_of_pointwise_equal hcomp hfg

end Computability
end FoC

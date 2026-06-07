import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Computable functions

## Encoding string functions

The book's computable functions operate on strings.  This module represents
input and output encodings explicitly and defines total and partial
Turing-computable string functions in terms of machine output behavior.

## Book coordinates

Used by:
- Chapter 5, Section 5.1: Turing-computable string functions.
- Chapter 5, Section 5.2: recursively enumerable languages as ranges of
  computable functions.
-/

namespace FoC
namespace Computability

open Languages

/-!
# Word encodings

Computable functions may use separate input and output alphabets. Encoding maps
lift symbol encodings to words while preserving the word operations needed
later.
-/

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

/-!
# Total computable functions

A total string function is computed when the machine halts on every encoded
input with the encoded output word.
-/

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

/-!
# Partial computable functions

Partial functions are represented by options. Undefined inputs correspond to
nonhalting machine behavior.
-/

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

def TotalAsPartial (f : Word input -> Word output) :
    Word input -> Option (Word output) :=
  fun w => some (f w)

def PartialFunctionDomain
  (f : Word input -> Option (Word output)) : Language input :=
  fun w => exists out : Word output, f w = some out

/-!
# Total-to-partial bridge

Every total computable function is a partial computable function with universal
domain.
-/

theorem computes_function_halts {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Word output}
    (h : ComputesFunction M encodeInput encodeOutput f) (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) :=
  TuringMachine.halts_with_output_implies_halts (h w)

theorem computesFunction_to_partial
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Word output}
    (h : ComputesFunction M encodeInput encodeOutput f) :
    ComputesPartialFunction M encodeInput encodeOutput (TotalAsPartial f) := by
  intro w
  exact h w

theorem turingComputable_to_partial
    {f : Word input -> Word output}
    (h : TuringComputable f) :
    TuringComputablePartial (TotalAsPartial f) := by
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
                      exact ⟨symbol, state, M, encodeInput, encodeOutput,
                        computesFunction_to_partial hcomp⟩

theorem partialFunctionDomain_mem
    {f : Word input -> Option (Word output)} (w : Word input) :
    w ∈ PartialFunctionDomain f <->
      exists out : Word output, f w = some out :=
  Iff.rfl

theorem totalAsPartial_domain_universal
    (f : Word input -> Word output) :
    Language.Equal (PartialFunctionDomain (TotalAsPartial f))
      (Language.Universal : Language input) := by
  intro w
  constructor
  · intro _h
    trivial
  · intro _h
    exact Exists.intro (f w) rfl

theorem computesPartialFunction_halts_iff_domain
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f : Word input -> Option (Word output)}
    (h : ComputesPartialFunction M encodeInput encodeOutput f)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) <->
      w ∈ PartialFunctionDomain f := by
  constructor
  · intro hhalt
    cases hf : f w with
    | none =>
        have hw := h w
        rw [hf] at hw
        exact False.elim (hw hhalt)
    | some out =>
        exact Exists.intro out hf
  · intro hdomain
    cases hdomain with
    | intro out hout =>
        have hw := h w
        rw [hout] at hw
        exact TuringMachine.halts_with_output_implies_halts hw

/-!
# Extensionality

Computability and partial-function domains are invariant under pointwise equal
functions.
-/

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

theorem partialFunctionDomain_equal_of_pointwise
    {f g : Word input -> Option (Word output)}
    (hfg : forall w, f w = g w) :
    Language.Equal (PartialFunctionDomain f) (PartialFunctionDomain g) := by
  intro w
  constructor
  · intro hdomain
    cases hdomain with
    | intro out hout =>
        exists out
        rw [← hfg w]
        exact hout
  · intro hdomain
    cases hdomain with
    | intro out hout =>
        exists out
        rw [hfg w]
        exact hout

theorem computesPartialFunction_of_pointwise_equal
    {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {encodeOutput : output -> symbol}
    {f g : Word input -> Option (Word output)}
    (h : ComputesPartialFunction M encodeInput encodeOutput f)
    (hfg : forall w, f w = g w) :
    ComputesPartialFunction M encodeInput encodeOutput g := by
  intro w
  rw [← hfg w]
  exact h w

theorem turingComputablePartial_of_pointwise_equal
    {f g : Word input -> Option (Word output)}
    (h : TuringComputablePartial f) (hfg : forall w, f w = g w) :
    TuringComputablePartial g := by
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
                      exact computesPartialFunction_of_pointwise_equal
                        hcomp hfg

end Computability
end FoC

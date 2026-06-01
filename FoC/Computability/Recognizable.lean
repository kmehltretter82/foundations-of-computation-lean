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

def TuringDecidable (L : Language input) : Prop :=
  exists symbol : Type, exists state : Type,
    exists M : TuringMachine symbol state,
      exists encodeInput : input -> symbol,
        exists zero : symbol, exists one : symbol,
          DecidesLanguage M encodeInput zero one L

def Recursive (L : Language input) : Prop :=
  TuringDecidable L

def RecursivelyEnumerable (L : Language input) : Prop :=
  TuringAcceptable L

theorem decider_halts_on_all_inputs {M : TuringMachine symbol state}
    {encodeInput : input -> symbol} {zero one : symbol}
    {L : Language input}
    (h : DecidesLanguage M encodeInput zero one L)
    (w : Word input) :
    TuringMachine.HaltsOnInput M (EncodeWord encodeInput w) := by
  by_cases hw : w ∈ L
  · exact TuringMachine.halts_with_output_implies_halts ((h w).left hw)
  · exact TuringMachine.halts_with_output_implies_halts ((h w).right hw)

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

theorem recursive_complement {L : Language input}
    (h : Recursive L) : Recursive (Language.Compl L) :=
  turing_decidable_complement h

end Computability
end FoC

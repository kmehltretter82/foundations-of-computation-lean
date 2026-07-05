import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic
import FoC.Computability.Compiler.Core.CommonGround.SearchAlgebra

set_option doc.verso true

/-!
# Tuple-search algebra for finite recognizers

Pure existential algebra for bounded and unbounded dovetailing.  These lemmas
keep generated-search construction files focused on finite machines rather than
reproving the same conversions between ordinary halting and hidden exact fuel.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace TupleSearch

universe uSymbol uState uLeft uRight

/--
Generic pair-bounding algebra for dovetail drivers.
-/
theorem exists_bounded_pair_iff_exists_pair
    (P : Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
        m <= limit /\ n <= limit /\ P m n) <->
      exists m : Nat, exists n : Nat, P m n := by
  exact CommonGround.exists_bounded_pair_iff_exists_pair P

/--
Generic triple-bounding algebra for dovetail drivers.
-/
theorem exists_bounded_triple_iff_exists_triple
    (P : Nat -> Nat -> Nat -> Prop) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m <= limit /\ n <= limit /\ fuel <= limit /\ P m n fuel) <->
      exists m : Nat, exists n : Nat, exists fuel : Nat, P m n fuel := by
  exact CommonGround.exists_bounded_triple_iff_exists_triple P

/--
Search over an explicit fuel component is equivalent to ordinary halting for
some generated input.
-/
theorem exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
    {symbol : Type uSymbol} {state : Type uState}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Word symbol) :
    (exists m : Nat,
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn M fuel (inputOf m)) <->
      exists m : Nat,
        TuringMachine.HaltsOnInput M (inputOf m) := by
  constructor
  · intro h
    rcases h with ⟨m, fuel, hfuel⟩
    exact
      ⟨m,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, fuel, hfuel⟩

/--
Bounded dovetailing over a generated input index and an explicit fuel is
equivalent to ordinary halting for some generated input.
-/
theorem exists_bounded_pair_haltsOnInputIn_iff_exists_haltsOnInput
    {symbol : Type uSymbol} {state : Type uState}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Word symbol) :
    (exists limit : Nat,
      exists m : Nat,
      exists fuel : Nat,
        m <= limit /\
          fuel <= limit /\
          TuringMachine.HaltsOnInputIn M fuel (inputOf m)) <->
      exists m : Nat,
        TuringMachine.HaltsOnInput M (inputOf m) := by
  exact
    Iff.trans
      (exists_bounded_pair_iff_exists_pair
        (fun m fuel =>
          TuringMachine.HaltsOnInputIn M fuel (inputOf m)))
      (exists_pair_haltsOnInputIn_iff_exists_haltsOnInput
        M inputOf)

/--
Search over two generated indices and a hidden exact fuel is equivalent to
ordinary halting for some generated pair input.
-/
theorem exists_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
    {symbol : Type uSymbol} {state : Type uState}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Nat -> Word symbol) :
    (exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        TuringMachine.HaltsOnInputIn M fuel (inputOf m n)) <->
      exists m : Nat,
      exists n : Nat,
        TuringMachine.HaltsOnInput M (inputOf m n) := by
  constructor
  · intro h
    rcases h with ⟨m, n, fuel, hfuel⟩
    exact
      ⟨m, n,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, n, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, n, fuel, hfuel⟩

/--
Bounded dovetailing over two generated indices and a hidden exact fuel is
equivalent to ordinary halting for some generated pair input.
-/
theorem exists_bounded_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
    {symbol : Type uSymbol} {state : Type uState}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Nat -> Word symbol) :
    (exists limit : Nat,
      exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m <= limit /\
          n <= limit /\
          fuel <= limit /\
          TuringMachine.HaltsOnInputIn M fuel (inputOf m n)) <->
      exists m : Nat,
      exists n : Nat,
        TuringMachine.HaltsOnInput M (inputOf m n) := by
  exact
    Iff.trans
      (exists_bounded_triple_iff_exists_triple
        (fun m n fuel =>
          TuringMachine.HaltsOnInputIn M fuel (inputOf m n)))
      (exists_triple_haltsOnInputIn_iff_exists_pair_haltsOnInput
        M inputOf)

/--
For a fixed public budget on generated indices, hiding selected exact fuel is
equivalent to ordinary selected-machine halting.
-/
theorem exists_bounded_pair_haltsOnInputIn_iff_exists_bounded_pair_haltsOnInput
    {symbol : Type uSymbol} {state : Type uState}
    (M : TuringMachine symbol state)
    (inputOf : Nat -> Nat -> Word symbol)
    (budget : Nat) :
    (exists m : Nat,
      exists n : Nat,
      exists fuel : Nat,
        m <= budget /\
          n <= budget /\
          TuringMachine.HaltsOnInputIn M fuel (inputOf m n)) <->
      exists m : Nat,
      exists n : Nat,
        m <= budget /\
          n <= budget /\
          TuringMachine.HaltsOnInput M (inputOf m n) := by
  constructor
  · intro h
    rcases h with ⟨m, n, fuel, hm, hn, hfuel⟩
    exact
      ⟨m, n, hm, hn,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := fuel) hfuel⟩
  · intro h
    rcases h with ⟨m, n, hm, hn, hhalt⟩
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hhalt with
      ⟨fuel, hfuel⟩
    exact ⟨m, n, fuel, hm, hn, hfuel⟩

/--
Two exact-fuel witnesses for the same input are equivalent to ordinary
halting of both machines on that input.
-/
theorem exists_pair_haltsOnInputIn_and_iff_haltsOnInput_and
    {symbol : Type uSymbol}
    {leftState : Type uLeft} {rightState : Type uRight}
    (left : TuringMachine symbol leftState)
    (right : TuringMachine symbol rightState)
    (input : Word symbol) :
    (exists leftFuel : Nat,
      exists rightFuel : Nat,
        TuringMachine.HaltsOnInputIn left leftFuel input /\
          TuringMachine.HaltsOnInputIn right rightFuel input) <->
      TuringMachine.HaltsOnInput left input /\
        TuringMachine.HaltsOnInput right input := by
  constructor
  · intro h
    rcases h with ⟨leftFuel, rightFuel, hleft, hright⟩
    exact
      ⟨TuringMachine.halts_on_input_in_to_halts_on_input
          (n := leftFuel) hleft,
        TuringMachine.halts_on_input_in_to_halts_on_input
          (n := rightFuel) hright⟩
  · intro h
    rcases h with ⟨hleft, hright⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hleft with
      ⟨leftFuel, hleftFuel⟩
    rcases TuringMachine.halts_on_input_to_halts_on_input_in
        hright with
      ⟨rightFuel, hrightFuel⟩
    exact ⟨leftFuel, rightFuel, hleftFuel, hrightFuel⟩

end TupleSearch
end FiniteRecognizer

end Computability
end FoC

import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition

set_option doc.verso true

/-!
# Initial exact-fuel layout materializer contract

Semantic contract for the first output-producing phase of the exact-fuel stage
program.  This phase parses a unary fuel prefix and emits the protected
initial exact-fuel layout for the selected machine.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StageProgram

def InitialLayoutMaterializerSpec {stateCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  OutputSpec materializer (Layout.stageCodeToInitialLayoutCode M)

def InitialLayoutMaterializerConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists materializerState : Type,
  exists materializer : TuringMachine MachineCodeSymbol materializerState,
    InitialLayoutMaterializerSpec materializer M

theorem stageCodeToInitialLayoutCode_eq_some_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens output : Word MachineCodeSymbol) :
    Layout.stageCodeToInitialLayoutCode M tokens = some output <->
      exists input : Word MachineCodeSymbol,
      exists fuel : Nat,
        tokens = stageCode input fuel /\
          output = Layout.encode (Layout.initial M input fuel) := by
  constructor
  · intro h
    unfold Layout.stageCodeToInitialLayoutCode at h
    cases hdecode : MachineDescription.decodeNat tokens with
    | none =>
        rw [hdecode] at h
        cases h
    | some decoded =>
        rcases decoded with ⟨fuel, input⟩
        rw [hdecode] at h
        cases h
        exact
          ⟨input, fuel,
            stageCode_eq_of_decodeNat hdecode, rfl⟩
  · intro h
    rcases h with ⟨input, fuel, htokens, houtput⟩
    subst tokens
    subst output
    simpa [stageCode] using
      Layout.stageCodeToInitialLayoutCode_stageCode M input fuel

theorem stageCodeToInitialLayoutCode_eq_none_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Layout.stageCodeToInitialLayoutCode M tokens = none <->
      MachineDescription.decodeNat tokens = none := by
  constructor
  · intro h
    unfold Layout.stageCodeToInitialLayoutCode at h
    cases hdecode : MachineDescription.decodeNat tokens with
    | none => rfl
    | some decoded =>
        rw [hdecode] at h
        cases h
  · intro hdecode
    simp [Layout.stageCodeToInitialLayoutCode, hdecode]

theorem stageCodeToInitialLayoutCode_eq_some_stageCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat)
    (output : Word MachineCodeSymbol) :
    Layout.stageCodeToInitialLayoutCode M (stageCode input fuel) =
        some output <->
      output = Layout.encode (Layout.initial M input fuel) := by
  rw [stageCodeToInitialLayoutCode_eq_some_iff]
  constructor
  · intro h
    rcases h with ⟨input', fuel', htokens, houtput⟩
    have hinj :
        fuel = fuel' /\ input = input' := by
      have hdecode := congrArg MachineDescription.decodeNat htokens
      simp [stageCode, MachineDescription.decodeNat_encodeNatAppend]
        at hdecode
      exact ⟨hdecode.left, hdecode.right⟩
    rcases hinj with ⟨hfuel, hinput⟩
    subst fuel'
    subst input'
    exact houtput
  · intro houtput
    exact ⟨input, fuel, rfl, houtput⟩

theorem initialLayoutMaterializerConstructionFiniteLeaf {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    InitialLayoutMaterializerConstruction M := by
  cases stateCount with
  | zero =>
      exact False.elim (Fin.elim0 M.start)
  | succ _ =>
      sorry

theorem initialLayoutMaterializerSpec_stageCode_output
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutMaterializerSpec materializer M)
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    TuringMachine.HaltsWithOutput materializer
      (stageCode input fuel)
      (Layout.encode (Layout.initial M input fuel)) := by
  exact
    (hmaterializer (stageCode input fuel)
      (Layout.encode (Layout.initial M input fuel))).mpr
      (by
        simpa [stageCode] using
          Layout.stageCodeToInitialLayoutCode_stageCode M input fuel)

theorem initialLayoutMaterializerSpec_haltsWithOutput_iff
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutMaterializerSpec materializer M)
    (tokens output : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput materializer tokens output <->
      exists input : Word MachineCodeSymbol,
      exists fuel : Nat,
        tokens = stageCode input fuel /\
          output = Layout.encode (Layout.initial M input fuel) := by
  exact Iff.trans (hmaterializer tokens output)
    (stageCodeToInitialLayoutCode_eq_some_iff M tokens output)

theorem initialLayoutMaterializerSpec_output_shape
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutMaterializerSpec materializer M)
    {tokens output : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsWithOutput materializer tokens output) :
    exists input : Word MachineCodeSymbol,
    exists fuel : Nat,
      tokens = stageCode input fuel /\
        output = Layout.encode (Layout.initial M input fuel) := by
  exact
    (initialLayoutMaterializerSpec_haltsWithOutput_iff
      hmaterializer tokens output).mp hhalt

end StageProgram
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

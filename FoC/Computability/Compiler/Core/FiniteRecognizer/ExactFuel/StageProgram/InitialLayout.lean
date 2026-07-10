import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition
import FoC.Computability.MachineBuilder.TapeCode

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

def InitialLayoutExactMaterializerSpec {stateCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  ExactOutputSpec materializer (Layout.stageCodeToInitialLayoutCode M)

def InitialLayoutMaterializerConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists materializerState : Type,
  exists materializer : TuringMachine MachineCodeSymbol materializerState,
    InitialLayoutMaterializerSpec materializer M

def InitialLayoutExactMaterializerConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists materializerState : Type,
  exists materializer : TuringMachine MachineCodeSymbol materializerState,
    InitialLayoutExactMaterializerSpec materializer M ∧
      ExactOutputCanonicalSpec materializer
        (Layout.stageCodeToInitialLayoutCode M) ∧
        TuringMachine.HaltingTransitionsDisabled materializer

def initialLayoutDecodedOutput {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Layout.encode (Layout.initial M input fuel)

/--
Executable code primitive for the initial-layout materializer.  This is not
yet the finite transition table; it is the precise code-level transformer that
the finite materializer leaf must realize.
-/
def initialLayoutMaterializerCodePrimitive {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    MachineDescription.TapeCodePrimitive where
  transform := Layout.stageCodeToInitialLayoutCode M

def InitialLayoutMaterializerPrimitiveSpec {stateCount : Nat}
    (primitive : MachineDescription.TapeCodePrimitive)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  primitive.Realizes (Layout.stageCodeToInitialLayoutCode M)

theorem initialLayoutMaterializerCodePrimitive_realizes
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    InitialLayoutMaterializerPrimitiveSpec
      (initialLayoutMaterializerCodePrimitive M) M := by
  intro tokens
  rfl

theorem initialLayoutMaterializerCodePrimitive_transform_eq_decodeNat
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    (initialLayoutMaterializerCodePrimitive M).transform tokens =
      match MachineDescription.decodeNat tokens with
      | none => none
      | some (fuel, input) =>
          some (initialLayoutDecodedOutput M fuel input) := by
  cases hdecode : MachineDescription.decodeNat tokens with
  | none =>
      simp [initialLayoutMaterializerCodePrimitive,
        Layout.stageCodeToInitialLayoutCode, hdecode]
  | some decoded =>
      rcases decoded with ⟨fuel, input⟩
      simp [initialLayoutMaterializerCodePrimitive,
        Layout.stageCodeToInitialLayoutCode,
        initialLayoutDecodedOutput, hdecode]

theorem initialLayoutDecodedOutput_empty {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    initialLayoutDecodedOutput M fuel
        ([] : Word MachineCodeSymbol) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeNatAppend M.start.val
            (encodeOptionalCodeSymbolsAppend []
              (encodeOptionalCodeSymbolAppend none
                (encodeOptionalCodeSymbolsAppend [] [])))) := by
  simpa [initialLayoutDecodedOutput] using
    Layout.encode_initial_empty M fuel

theorem initialLayoutDecodedOutput_cons {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    initialLayoutDecodedOutput M fuel (symbol :: rest) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeNatAppend M.start.val
            (encodeOptionalCodeSymbolsAppend []
              (encodeOptionalCodeSymbolAppend (some symbol)
                (encodeOptionalCodeSymbolsAppend
                  (rest.map some) [])))) := by
  simpa [initialLayoutDecodedOutput] using
    Layout.encode_initial_cons M symbol rest fuel

def InitialLayoutDecodedExactOutputForwardSpec {stateCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall input : Word MachineCodeSymbol,
  forall fuel : Nat,
    TuringMachine.HaltsWithExactOutput materializer
      (stageCode input fuel)
      (initialLayoutDecodedOutput M fuel input)

def InitialLayoutDecodedExactOutputClosedSpec {stateCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall tokens output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithExactOutput materializer tokens output ->
      exists input : Word MachineCodeSymbol,
      exists fuel : Nat,
        tokens = stageCode input fuel /\
          output = initialLayoutDecodedOutput M fuel input

def InitialLayoutDecodedExactOutputSpec {stateCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  InitialLayoutDecodedExactOutputForwardSpec materializer M ∧
    InitialLayoutDecodedExactOutputClosedSpec materializer M

/--
Finite-machine target for realizing the initial-layout primitive with exact
canonical output.  This is the sharper construction boundary behind
{name}`InitialLayoutExactMaterializerConstruction`.
-/
def InitialLayoutExactOutputPrimitiveConstruction {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists materializerState : Type,
  exists materializer : TuringMachine MachineCodeSymbol materializerState,
    ExactOutputSpec materializer
        (initialLayoutMaterializerCodePrimitive M).transform ∧
      ExactOutputCanonicalSpec materializer
        (initialLayoutMaterializerCodePrimitive M).transform ∧
      TuringMachine.HaltingTransitionsDisabled materializer

def InitialLayoutExactOutputPrimitiveFinStateConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    InitialLayoutExactOutputPrimitiveConstruction M

def InitialLayoutDecodedExactOutputPrimitiveConstruction
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists materializerState : Type,
  exists materializer : TuringMachine MachineCodeSymbol materializerState,
    InitialLayoutDecodedExactOutputSpec materializer M ∧
      ExactOutputCanonicalSpec materializer
        (Layout.stageCodeToInitialLayoutCode M) ∧
        TuringMachine.HaltingTransitionsDisabled materializer

def InitialLayoutDecodedExactOutputPrimitiveFinStateConstruction : Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    InitialLayoutDecodedExactOutputPrimitiveConstruction M

theorem initialLayoutExactMaterializerConstruction_of_exactOutputPrimitive
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hprimitive : InitialLayoutExactOutputPrimitiveConstruction M) :
    InitialLayoutExactMaterializerConstruction M := by
  rcases hprimitive with
    ⟨materializerState, materializer, hexact,
      hcanonical, hstop⟩
  refine
    ⟨materializerState, materializer, ?_, ?_, hstop⟩
  · simpa [InitialLayoutExactMaterializerSpec,
      initialLayoutMaterializerCodePrimitive] using hexact
  · simpa [initialLayoutMaterializerCodePrimitive] using hcanonical

theorem initialLayoutMaterializerCodePrimitive_stageCode
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (initialLayoutMaterializerCodePrimitive M).transform
        (stageCode input fuel) =
      some (Layout.encode (Layout.initial M input fuel)) := by
  simpa [initialLayoutMaterializerCodePrimitive, stageCode] using!
    Layout.stageCodeToInitialLayoutCode_stageCode M input fuel

theorem initialLayoutMaterializerSpec_of_exact_canonical
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hexact : InitialLayoutExactMaterializerSpec materializer M)
    (hcanonical :
      ExactOutputCanonicalSpec materializer
        (Layout.stageCodeToInitialLayoutCode M)) :
    InitialLayoutMaterializerSpec materializer M :=
  outputSpec_of_exactOutput_canonical hexact hcanonical

theorem initialLayoutMaterializerConstruction_of_exact
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (h : InitialLayoutExactMaterializerConstruction M) :
    InitialLayoutMaterializerConstruction M := by
  rcases h with
    ⟨materializerState, materializer, hexact,
      hcanonical, _hstop⟩
  exact
    ⟨materializerState, materializer,
      initialLayoutMaterializerSpec_of_exact_canonical
        hexact hcanonical⟩

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
    simpa [stageCode, GeneratedCode.stageCode] using
      Layout.stageCodeToInitialLayoutCode_stageCode M input fuel

theorem stageCodeToInitialLayoutCode_eq_some_cons_cons
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {tokens output : Word MachineCodeSymbol}
    (h : Layout.stageCodeToInitialLayoutCode M tokens = some output) :
    exists second : MachineCodeSymbol,
    exists rest : Word MachineCodeSymbol,
      output = MachineCodeSymbol.header :: second :: rest := by
  rcases
      (stageCodeToInitialLayoutCode_eq_some_iff
        M tokens output).mp h with
    ⟨input, fuel, _htokens, houtput⟩
  subst output
  exact Layout.encode_cons_cons (Layout.initial M input fuel)

theorem outputThenRecognizeHandoffTape_stageCodeToInitialLayoutCode
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {tokens output : Word MachineCodeSymbol}
    (h : Layout.stageCodeToInitialLayoutCode M tokens = some output) :
    outputThenRecognizeHandoffTape (Tape.output output) =
      Tape.input output := by
  rcases stageCodeToInitialLayoutCode_eq_some_cons_cons M h with
    ⟨second, rest, houtput⟩
  rw [houtput]
  exact
    outputThenRecognizeHandoffTape_output_cons_cons
      MachineCodeSymbol.header second rest

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
      exact
        GeneratedCode.stageCode_injective
          (by simpa [stageCode] using htokens)
    rcases hinj with ⟨hfuel, hinput⟩
    subst fuel'
    subst input'
    exact houtput
  · intro houtput
    exact ⟨input, fuel, rfl, houtput⟩

theorem stageCodeToInitialLayoutCode_stageCode_empty {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    Layout.stageCodeToInitialLayoutCode M
        (stageCode ([] : Word MachineCodeSymbol) fuel) =
      some
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend fuel
            (MachineDescription.encodeNatAppend M.start.val
              (encodeOptionalCodeSymbolsAppend []
                (encodeOptionalCodeSymbolAppend none
                  (encodeOptionalCodeSymbolsAppend [] []))))) := by
  simpa [stageCode, GeneratedCode.stageCode,
    Layout.encode_initial_empty] using!
    Layout.stageCodeToInitialLayoutCode_stageCode
      M ([] : Word MachineCodeSymbol) fuel

theorem stageCodeToInitialLayoutCode_stageCode_empty_expanded
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    Layout.stageCodeToInitialLayoutCode M
        (stageCode ([] : Word MachineCodeSymbol) fuel) =
      some
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend fuel
            (MachineDescription.encodeNatAppend M.start.val
              (MachineDescription.encodeNatAppend 0
                (MachineDescription.encodeNatAppend 0
                  (MachineDescription.encodeNatAppend 0 []))))) := by
  simpa [stageCode, GeneratedCode.stageCode,
    Layout.encode_initial_empty_expanded] using!
    Layout.stageCodeToInitialLayoutCode_stageCode
      M ([] : Word MachineCodeSymbol) fuel

theorem stageCodeToInitialLayoutCode_stageCode_cons {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    Layout.stageCodeToInitialLayoutCode M
        (stageCode (symbol :: rest) fuel) =
      some
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend fuel
            (MachineDescription.encodeNatAppend M.start.val
              (encodeOptionalCodeSymbolsAppend []
                (encodeOptionalCodeSymbolAppend (some symbol)
                  (encodeOptionalCodeSymbolsAppend
                    (rest.map some) []))))) := by
  simpa [stageCode, GeneratedCode.stageCode,
    Layout.encode_initial_cons] using!
    Layout.stageCodeToInitialLayoutCode_stageCode
      M (symbol :: rest) fuel

theorem stageCodeToInitialLayoutCode_stageCode_cons_expanded
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    Layout.stageCodeToInitialLayoutCode M
        (stageCode (symbol :: rest) fuel) =
      some
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend fuel
            (MachineDescription.encodeNatAppend M.start.val
              (MachineDescription.encodeNatAppend 0
                (MachineDescription.encodeNatAppend
                  (codeSymbolTag symbol + 1)
                  (encodeOptionalCodeSymbolsAppend
                    (rest.map some) []))))) := by
  simpa [stageCode, GeneratedCode.stageCode,
    Layout.encode_initial_cons_expanded] using!
    Layout.stageCodeToInitialLayoutCode_stageCode
      M (symbol :: rest) fuel

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
        simpa [stageCode] using!
          Layout.stageCodeToInitialLayoutCode_stageCode M input fuel)

theorem initialLayoutExactMaterializerSpec_stageCode_exactOutput
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutExactMaterializerSpec materializer M)
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    TuringMachine.HaltsWithExactOutput materializer
      (stageCode input fuel)
      (Layout.encode (Layout.initial M input fuel)) := by
  exact
    (hmaterializer (stageCode input fuel)
      (Layout.encode (Layout.initial M input fuel))).mpr
      (by
        simpa [stageCode] using!
          Layout.stageCodeToInitialLayoutCode_stageCode M input fuel)

theorem initialLayoutExactMaterializerSpec_haltsWithExactOutput_iff
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutExactMaterializerSpec materializer M)
    (tokens output : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithExactOutput materializer tokens output <->
      exists input : Word MachineCodeSymbol,
      exists fuel : Nat,
        tokens = stageCode input fuel /\
          output = Layout.encode (Layout.initial M input fuel) := by
  exact Iff.trans (hmaterializer tokens output)
    (stageCodeToInitialLayoutCode_eq_some_iff M tokens output)

theorem initialLayoutExactMaterializerSpec_iff_decodedExactOutput
    {stateCount : Nat} {materializerState : Type}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    InitialLayoutExactMaterializerSpec materializer M <->
      InitialLayoutDecodedExactOutputSpec materializer M := by
  constructor
  · intro hmaterializer
    constructor
    · intro input fuel
      simpa [initialLayoutDecodedOutput] using
        initialLayoutExactMaterializerSpec_stageCode_exactOutput
          hmaterializer input fuel
    · intro tokens output hhalt
      rcases
          (initialLayoutExactMaterializerSpec_haltsWithExactOutput_iff
            hmaterializer tokens output).mp hhalt with
        ⟨input, fuel, htokens, houtput⟩
      exact
        ⟨input, fuel, htokens, by
          simpa [initialLayoutDecodedOutput] using houtput⟩
  · intro hdecoded
    intro tokens output
    constructor
    · intro hhalt
      rcases hdecoded.right tokens output hhalt with
        ⟨input, fuel, htokens, houtput⟩
      exact
        (stageCodeToInitialLayoutCode_eq_some_iff
          M tokens output).mpr
          ⟨input, fuel, htokens, by
            simpa [initialLayoutDecodedOutput] using houtput⟩
    · intro htransform
      rcases
          (stageCodeToInitialLayoutCode_eq_some_iff
            M tokens output).mp htransform with
        ⟨input, fuel, htokens, houtput⟩
      subst tokens
      subst output
      simpa [initialLayoutDecodedOutput] using
        hdecoded.left input fuel

theorem initialLayoutExactOutputPrimitiveConstruction_iff_decoded
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    InitialLayoutExactOutputPrimitiveConstruction M <->
      InitialLayoutDecodedExactOutputPrimitiveConstruction M := by
  constructor
  · intro hprimitive
    rcases hprimitive with
      ⟨materializerState, materializer, hexact,
        hcanonical, hstop⟩
    refine ⟨materializerState, materializer, ?_, hcanonical, hstop⟩
    exact
      (initialLayoutExactMaterializerSpec_iff_decodedExactOutput
        materializer M).mp
        (by
          simpa [InitialLayoutExactMaterializerSpec,
            initialLayoutMaterializerCodePrimitive] using hexact)
  · intro hdecoded
    rcases hdecoded with
      ⟨materializerState, materializer, hspec,
        hcanonical, hstop⟩
    refine ⟨materializerState, materializer, ?_, hcanonical, hstop⟩
    simpa [InitialLayoutExactMaterializerSpec,
      initialLayoutMaterializerCodePrimitive] using
      (initialLayoutExactMaterializerSpec_iff_decodedExactOutput
        materializer M).mpr hspec

theorem initialLayoutExactOutputPrimitiveFinStateConstruction_iff_decoded :
    InitialLayoutExactOutputPrimitiveFinStateConstruction <->
      InitialLayoutDecodedExactOutputPrimitiveFinStateConstruction := by
  constructor
  · intro hconstruction stateCount M
    exact
      (initialLayoutExactOutputPrimitiveConstruction_iff_decoded M).mp
        (hconstruction stateCount M)
  · intro hconstruction stateCount M
    exact
      (initialLayoutExactOutputPrimitiveConstruction_iff_decoded M).mpr
        (hconstruction stateCount M)

theorem initialLayoutExactMaterializerCanonical_output_shape
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hcanonical :
      ExactOutputCanonicalSpec materializer
        (Layout.stageCodeToInitialLayoutCode M))
    {tokens : Word MachineCodeSymbol}
    {final :
      TuringMachine.Configuration MachineCodeSymbol materializerState}
    (hcomp :
      TuringMachine.Computes materializer
        (TuringMachine.initial materializer tokens) final)
    (hhalt : TuringMachine.Halted materializer final) :
    exists input : Word MachineCodeSymbol,
    exists fuel : Nat,
      tokens = stageCode input fuel /\
        final.tape =
          Tape.output (Layout.encode (Layout.initial M input fuel)) := by
  rcases hcanonical tokens final hcomp hhalt with
    ⟨output, houtput, htape⟩
  rcases
      (stageCodeToInitialLayoutCode_eq_some_iff
        M tokens output).mp houtput with
    ⟨input, fuel, htokens, hshape⟩
  subst output
  exact ⟨input, fuel, htokens, htape⟩

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

theorem initialLayoutMaterializerSpec_stageCode_empty_output_iff
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutMaterializerSpec materializer M)
    (fuel : Nat) (output : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput materializer
        (stageCode ([] : Word MachineCodeSymbol) fuel) output <->
      output =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend fuel
            (MachineDescription.encodeNatAppend M.start.val
              (MachineDescription.encodeNatAppend 0
                (MachineDescription.encodeNatAppend 0
                  (MachineDescription.encodeNatAppend 0 [])))) := by
  exact Iff.trans
    (hmaterializer (stageCode ([] : Word MachineCodeSymbol) fuel) output)
    (by
      rw [stageCodeToInitialLayoutCode_stageCode_empty_expanded]
      constructor
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl)

theorem initialLayoutMaterializerSpec_stageCode_cons_output_iff
    {stateCount : Nat} {materializerState : Type}
    {materializer : TuringMachine MachineCodeSymbol materializerState}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (hmaterializer :
      InitialLayoutMaterializerSpec materializer M)
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat)
    (output : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput materializer
        (stageCode (symbol :: rest) fuel) output <->
      output =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend fuel
            (MachineDescription.encodeNatAppend M.start.val
              (MachineDescription.encodeNatAppend 0
                (MachineDescription.encodeNatAppend
                  (codeSymbolTag symbol + 1)
                  (encodeOptionalCodeSymbolsAppend
                    (rest.map some) [])))) := by
  exact Iff.trans
    (hmaterializer (stageCode (symbol :: rest) fuel) output)
    (by
      rw [stageCodeToInitialLayoutCode_stageCode_cons_expanded]
      constructor
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl)

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

import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionPaddingSplit

set_option doc.verso true

/-!
# Output contracts for the padding-aware selected footprint compactor

The exact selected-footprint compactor remains a finite-machine leaf.  The
padding split already exposes the right source and target shapes; this module
adds the matching normalized-output contracts and branch views so downstream
routes can consume the padding-aware endpoint without committing to the final
cursor position.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

/-! ## Generic output contracts -/

def GuardedLogicalTapeDecoderFootprintCompactorOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (selectedSegmentLogicalTapeDecoderPayloadCells bits padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintTargetTapeFromPayload
            bits padding))

def GuardedLogicalTapeDecoderFootprintCompactorOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    GuardedLogicalTapeDecoderFootprintCompactorOutputSpec compactor

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            bits padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
      compactor

theorem guardedLogicalTapeDecoderFootprintCompactorOutputSpec_of_exact
    {compactor : MachineDescription}
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorSpec compactor) :
    GuardedLogicalTapeDecoderFootprintCompactorOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun bits padding)

theorem guardedLogicalTapeDecoderFootprintCompactorOutputConstruction_of_exact
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      guardedLogicalTapeDecoderFootprintCompactorOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_exact
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_of_exact
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_exact
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_guardedOutputSpec
    {compactor : MachineDescription}
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rw [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_fromPayload]
  exact hrun bits padding

theorem guardedLogicalTapeDecoderFootprintCompactorOutputSpec_of_paddingSplitOutputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
        compactor) :
    GuardedLogicalTapeDecoderFootprintCompactorOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rw [← selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload,
    ← selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_fromPayload]
  exact hrun bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_of_guardedOutput
    (h :
      GuardedLogicalTapeDecoderFootprintCompactorOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_guardedOutputSpec
        hspec⟩

theorem guardedLogicalTapeDecoderFootprintCompactorOutputConstruction_of_paddingSplitOutput
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction) :
    GuardedLogicalTapeDecoderFootprintCompactorOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      guardedLogicalTapeDecoderFootprintCompactorOutputSpec_of_paddingSplitOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_iff_guardedOutputSpec
    (compactor : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
        compactor ↔
      GuardedLogicalTapeDecoderFootprintCompactorOutputSpec
        compactor := by
  constructor
  · exact
      guardedLogicalTapeDecoderFootprintCompactorOutputSpec_of_paddingSplitOutputSpec
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_guardedOutputSpec

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_iff_guardedOutputConstruction :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction ↔
      GuardedLogicalTapeDecoderFootprintCompactorOutputConstruction := by
  constructor
  · exact
      guardedLogicalTapeDecoderFootprintCompactorOutputConstruction_of_paddingSplitOutput
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_of_guardedOutput

/-! ## Output branch contracts -/

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          [] padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            [] padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeWithOutput
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        [] [])
      (Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] [])) ∧
    (forall (pad : Option Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          [] (pad :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            [] (pad :: padding)))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) []))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) (pad :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) (pad :: padding)))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorNilPadSymbolCaseOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeWithOutput
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        [] [])
      (Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] [])) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          [] (none :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            [] (none :: padding)))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          [] (some padBit :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            [] (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConsPadSymbolCaseOutputSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) [])
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) []))) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) (none :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) (none :: padding)))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          (bit :: rest) (some padBit :: padding))
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) (some padBit :: padding)))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
    (compactor : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorNilPadSymbolCaseOutputSpec
      compactor ∧
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorConsPadSymbolCaseOutputSpec
      compactor

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
      compactor

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec_of_outputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_⟩
  · intro padding
    exact hrun [] padding
  · intro bit rest padding
    exact hrun (bit :: rest) padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_caseOutputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
      compactor := by
  rcases h with ⟨hready, hnil, hcons⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      exact hnil padding
  | cons bit rest =>
      exact hcons bit rest padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputConstruction_of_output
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec_of_outputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_of_caseOutput
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_caseOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec_of_bitPaddingCaseOutputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec
      compactor := by
  rcases h with
    ⟨hready, hnilNil, hnilCons, hconsNil, hconsCons⟩
  refine ⟨hready, ?_, ?_⟩
  · intro padding
    cases padding with
    | nil =>
        exact hnilNil
    | cons pad padding =>
        exact hnilCons pad padding
  · intro bit rest padding
    cases padding with
    | nil =>
        exact hconsNil bit rest
    | cons pad padding =>
        exact hconsCons bit rest pad padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec_of_splitPadSymbolCaseOutputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
      compactor := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro pad padding
    cases pad with
    | none =>
        exact hnilNone padding
    | some padBit =>
        exact hnilSome padBit padding
  · intro bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone bit rest padding
    | some padBit =>
        exact hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_outputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_splitPadSymbolCaseOutputSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
      compactor := by
  have hbit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorBitPaddingCaseOutputSpec_of_splitPadSymbolCaseOutputSpec
      h
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_caseOutputSpec
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorCaseOutputSpec_of_bitPaddingCaseOutputSpec
        hbit)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction_of_output
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_outputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_of_splitPadSymbolCasesOutput
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_splitPadSymbolCaseOutputSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_iff_splitPadSymbolCaseOutputSpec
    (compactor : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec
        compactor ↔
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
        compactor := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_outputSpec
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_splitPadSymbolCaseOutputSpec

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_iff_splitPadSymbolCaseOutputConstruction :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction_of_output
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputConstruction_of_splitPadSymbolCasesOutput

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_exact
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
        compactor) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec
      compactor := by
  have hspec :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec
        compactor :=
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSpec_of_splitSpec
      h
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_outputSpec
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorOutputSpec_of_exact
        hspec)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction_of_exact
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitPadSymbolCaseOutputSpec_of_exact
        hspec⟩

/-! ## Named output equalities -/

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_normalizedOutput
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputSource_eq_bits_padding
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_normalizedOutput
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTarget_output_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding) =
      Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding) := by
  exact
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTarget_normalizedOutput_eq
      bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTarget_nil_nil_output :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] []) =
      [] := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTarget_nil_none_output
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] (none :: padding)) =
      padding.filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTarget_nil_some_output
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] (some padBit :: padding)) =
      padBit :: padding.filterMap (fun cell => cell) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTarget_cons_nil_output
    (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) []) =
      bit :: rest := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding]
  simp

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTarget_cons_none_output
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) (none :: padding)) =
      List.append (bit :: rest) (padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding]
  rfl

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTarget_cons_some_output
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) (some padBit :: padding)) =
      List.append (bit :: rest)
        (padBit :: padding.filterMap (fun cell => cell)) := by
  rw [selectedSegmentLogicalTapeDecoderFootprintPaddingSplitOutputTarget_eq_bits_padding]
  rfl

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

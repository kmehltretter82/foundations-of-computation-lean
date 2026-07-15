import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Layout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Semantics
import FoC.Computability.TapeLemmas

set_option doc.verso true

/-!
# Delimiter-protected strict-probe frames

The strict exact-fuel probe keeps its current
{name (full := FoC.Computability.FiniteRecognizer.ExactFuel.Layout)}`Layout`
in the existing canonical encoding.  An immutable caller tag and caller-owned
suffix follow that encoding.  The decoder therefore identifies the exact
layout boundary without relying on a symbol that is absent from layout data.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Frame

/-- Immutable boundary between the strict-probe frame and caller-owned data. -/
def callerTag : MachineCodeSymbol := MachineCodeSymbol.moveRight

/-- A canonical exact-fuel layout followed by its protected caller suffix. -/
def protectedWord {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Layout.encodeAppend L (callerTag :: callerData)

/-- Decoding a protected frame returns both its exact layout and caller suffix. -/
theorem decode_protectedWord {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Layout.decode stateCount (protectedWord L callerData) =
      some (L, callerTag :: callerData) := by
  exact Layout.decode_encodeAppend L (callerTag :: callerData)

private theorem encodeOptionalCodeSymbolAppend_append
    (cell : Option MachineCodeSymbol)
    (suffix tail : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolAppend cell (List.append suffix tail) =
      List.append (encodeOptionalCodeSymbolAppend cell suffix) tail := by
  simp [encodeOptionalCodeSymbolAppend,
    MachineDescription.encodeNatAppend, List.append_assoc]

private theorem encodeOptionalCodeSymbolsPayloadAppend_append
    (cells : List (Option MachineCodeSymbol))
    (suffix tail : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolsPayloadAppend cells
        (List.append suffix tail) =
      List.append
        (encodeOptionalCodeSymbolsPayloadAppend cells suffix) tail := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp only [encodeOptionalCodeSymbolsPayloadAppend]
      rw [ih, encodeOptionalCodeSymbolAppend_append]

private theorem encodeOptionalCodeSymbolsAppend_append
    (cells : List (Option MachineCodeSymbol))
    (suffix tail : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolsAppend cells (List.append suffix tail) =
      List.append (encodeOptionalCodeSymbolsAppend cells suffix) tail := by
  simp only [encodeOptionalCodeSymbolsAppend]
  rw [encodeOptionalCodeSymbolsPayloadAppend_append]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

/-- Appending a suffix to a layout does not change its canonical prefix. -/
theorem layoutEncodeAppend_eq_append {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    Layout.encodeAppend L suffix =
      List.append (Layout.encode L) suffix := by
  cases L with
  | mk fuel state left head right =>
      change
        MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend fuel
              (MachineDescription.encodeNatAppend state.val
                (encodeOptionalCodeSymbolsAppend left
                  (encodeOptionalCodeSymbolAppend head
                    (encodeOptionalCodeSymbolsAppend right suffix)))) =
          List.append
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend fuel
                (MachineDescription.encodeNatAppend state.val
                  (encodeOptionalCodeSymbolsAppend left
                    (encodeOptionalCodeSymbolAppend head
                      (encodeOptionalCodeSymbolsAppend right [])))))
            suffix
      rw [show encodeOptionalCodeSymbolsAppend right suffix =
          List.append (encodeOptionalCodeSymbolsAppend right []) suffix by
        simpa using
          encodeOptionalCodeSymbolsAppend_append right [] suffix]
      rw [encodeOptionalCodeSymbolAppend_append]
      rw [encodeOptionalCodeSymbolsAppend_append]
      simp [MachineDescription.encodeNatAppend, List.append_assoc]

/-- The caller tag and caller data are a literal suffix of a protected frame. -/
theorem protectedWord_eq_encode_append {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    protectedWord L callerData =
      List.append (Layout.encode L) (callerTag :: callerData) := by
  exact layoutEncodeAppend_eq_append L (callerTag :: callerData)

/-- Equal protected frames have equal layouts and equal caller-owned data. -/
theorem protectedWord_injective {stateCount : Nat}
    {L₁ L₂ : Layout stateCount}
    {callerData₁ callerData₂ : Word MachineCodeSymbol}
    (h : protectedWord L₁ callerData₁ =
      protectedWord L₂ callerData₂) :
    L₁ = L₂ ∧ callerData₁ = callerData₂ := by
  have hdecode := congrArg (Layout.decode stateCount) h
  rw [decode_protectedWord, decode_protectedWord] at hdecode
  have hpairs :
      (L₁, callerTag :: callerData₁) =
        (L₂, callerTag :: callerData₂) :=
    Option.some.inj hdecode
  have hlayout : L₁ = L₂ := congrArg Prod.fst hpairs
  have hsuffix :
      callerTag :: callerData₁ = callerTag :: callerData₂ :=
    congrArg Prod.snd hpairs
  exact ⟨hlayout, (List.cons.inj hsuffix).2⟩

/--
Tape position immediately after the caller tag.  The head reads the first
caller-owned cell, or a blank when the caller suffix is empty.
-/
def afterCallerTape {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match callerData with
  | [] =>
      { left := (callerTag :: (Layout.encode L).reverse).map some
        head := none
        right := [] }
  | first :: rest =>
      { left := (callerTag :: (Layout.encode L).reverse).map some
        head := some first
        right := rest.map some }

/-- The post-tag tape retains the exact layout frame and caller-owned suffix. -/
theorem afterCallerTape_normalizedOutput {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Tape.normalizedOutput (afterCallerTape L callerData) =
      protectedWord L callerData := by
  rw [protectedWord_eq_encode_append]
  cases callerData <;>
    simp [afterCallerTape, Tape.normalizedOutput, Tape.cells,
      Function.comp_def]

/--
Forward-run representative with far-right blank padding.  The padding records
the visited physical window without changing the protected word.
-/
def afterCallerTapeWithRightPadding {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (padding : Nat) : Tape MachineCodeSymbol :=
  let clean := afterCallerTape L callerData
  { clean with
    right :=
      List.append clean.right
        (List.replicate padding (none : Option MachineCodeSymbol)) }

/-- Zero right padding is the clean semantic target. -/
theorem afterCallerTapeWithRightPadding_zero {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    afterCallerTapeWithRightPadding L callerData 0 =
      afterCallerTape L callerData := by
  simp [afterCallerTapeWithRightPadding]

/-- Far-right padding preserves the exact protected output word. -/
theorem afterCallerTapeWithRightPadding_normalizedOutput
    {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (padding : Nat) :
    Tape.normalizedOutput
        (afterCallerTapeWithRightPadding L callerData padding) =
      protectedWord L callerData := by
  rw [protectedWord_eq_encode_append]
  cases callerData <;>
    simp [afterCallerTapeWithRightPadding, afterCallerTape,
      Tape.normalizedOutput, Tape.cells, Function.comp_def]

/-- Far-right padding is equivalent to the clean post-tag tape. -/
theorem afterCallerTapeWithRightPadding_equiv {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (padding : Nat) :
    Tape.Equiv
      (afterCallerTapeWithRightPadding L callerData padding)
      (afterCallerTape L callerData) := by
  cases callerData with
  | nil =>
      refine ⟨rfl, rfl, ?_⟩
      change
        Tape.dropTrailingNone
            (List.replicate padding
              (none : Option MachineCodeSymbol)) = []
      exact dropTrailingNone_replicate_none padding
  | cons first rest =>
      simp [afterCallerTapeWithRightPadding, afterCallerTape,
        Tape.Equiv, dropTrailingNone_append_replicate_none]

/--
Physical exit currency for forward composition.  Closed inversion continues to
target the clean {name}`afterCallerTape`; forward runs may expose any equivalent
visited-window representative.
-/
def PhysicalExitTapeAt {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol) : Prop :=
  Tape.Equiv T (afterCallerTape L callerData)

/-- Every right-padded representative satisfies the physical exit contract. -/
theorem afterCallerTapeWithRightPadding_physicalExitTapeAt
    {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol)
    (padding : Nat) :
    PhysicalExitTapeAt L callerData
      (afterCallerTapeWithRightPadding L callerData padding) :=
  afterCallerTapeWithRightPadding_equiv L callerData padding

end Frame

/-!
## Exact semantic exits

The result is indexed by the exact remaining layout.  In particular, the
failure constructors do not discard the failed configuration even though
{name}`Outcome.failure` intentionally carries no payload.
-/

/--
A terminal strict-probe layout classified by its semantic outcome.  A failure
is terminal either because fuel is exhausted outside the halt state or because
a positive-fuel configuration has no next transition.
-/
inductive SemanticExitAt {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Outcome stateCount -> Layout stateCount -> Prop where
  /-- Exhausted fuel in the halt state is a successful exact exit. -/
  | success (L : Layout stateCount)
      (hfuel : L.fuel = 0)
      (hhalt : L.state = M.halt) :
      SemanticExitAt M (Outcome.success L.config) L
  /-- Exhausted fuel outside the halt state is a failed exact exit. -/
  | failureExhausted (L : Layout stateCount)
      (hfuel : L.fuel = 0)
      (hnotHalt : L.state ≠ M.halt) :
      SemanticExitAt M Outcome.failure L
  /-- A missing transition at positive fuel is a failed exact exit. -/
  | failureMissing (L : Layout stateCount) (fuel : Nat)
      (hfuel : L.fuel = fuel + 1)
      (htransition :
        M.transition L.state (Tape.read L.tape) = none) :
      SemanticExitAt M Outcome.failure L

/-- Every indexed terminal exit agrees with the generic strict semantics. -/
theorem semanticOutcome_eq_of_semanticExitAt
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {outcome : Outcome stateCount} {L : Layout stateCount}
    (hexit : SemanticExitAt M outcome L) :
    semanticOutcome M L.fuel L.config = outcome := by
  cases hexit with
  | success L hfuel hhalt =>
      simp [semanticOutcome, TuringMachine.runConfigExact?, hfuel,
        Layout.config, hhalt]
  | failureExhausted L hfuel hnotHalt =>
      simp [semanticOutcome, TuringMachine.runConfigExact?, hfuel,
        Layout.config, hnotHalt]
  | failureMissing L fuel hfuel htransition =>
      rw [hfuel]
      exact semanticOutcome_succ_of_transition_eq_none htransition

/--
An encoded terminal exit retains its semantic classification, exact layout,
immutable caller tag, and caller-owned data in one relation.
-/
structure EncodedExitAt {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outcome : Outcome stateCount) (L : Layout stateCount)
    (callerData tokens : Word MachineCodeSymbol) : Prop where
  semantic : SemanticExitAt M outcome L
  frame : tokens = Frame.protectedWord L callerData

/--
A physical terminal exit retains the exact semantic layout while observing its
tape only up to far-edge blank padding.
-/
structure PhysicalExitAt {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (outcome : Outcome stateCount) (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol)
    (T : Tape MachineCodeSymbol) : Prop where
  semantic : SemanticExitAt M outcome L
  frame : Frame.PhysicalExitTapeAt L callerData T

/-- Decoding an encoded exit recovers its exact layout and caller suffix. -/
theorem EncodedExitAt.decode
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {outcome : Outcome stateCount} {L : Layout stateCount}
    {callerData tokens : Word MachineCodeSymbol}
    (hexit : EncodedExitAt M outcome L callerData tokens) :
    Layout.decode stateCount tokens =
      some (L, Frame.callerTag :: callerData) := by
  rw [hexit.frame]
  exact Frame.decode_protectedWord L callerData

/-- An encoded exit has the semantic outcome named by its outcome index. -/
theorem EncodedExitAt.semanticOutcome
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {outcome : Outcome stateCount} {L : Layout stateCount}
    {callerData tokens : Word MachineCodeSymbol}
    (hexit : EncodedExitAt M outcome L callerData tokens) :
    semanticOutcome M L.fuel L.config = outcome :=
  semanticOutcome_eq_of_semanticExitAt hexit.semantic

/-- A physical exit has the semantic outcome named by its outcome index. -/
theorem PhysicalExitAt.semanticOutcome
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {outcome : Outcome stateCount} {L : Layout stateCount}
    {callerData : Word MachineCodeSymbol}
    {T : Tape MachineCodeSymbol}
    (hexit : PhysicalExitAt M outcome L callerData T) :
    semanticOutcome M L.fuel L.config = outcome :=
  semanticOutcome_eq_of_semanticExitAt hexit.semantic

/-- A physical exit preserves the exact protected frame as normalized output. -/
theorem PhysicalExitAt.normalizedOutput
    {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {outcome : Outcome stateCount} {L : Layout stateCount}
    {callerData : Word MachineCodeSymbol}
    {T : Tape MachineCodeSymbol}
    (hexit : PhysicalExitAt M outcome L callerData T) :
    Tape.normalizedOutput T = Frame.protectedWord L callerData := by
  exact (Tape.Equiv.normalizedOutput_eq hexit.frame).trans
    (Frame.afterCallerTape_normalizedOutput L callerData)

end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

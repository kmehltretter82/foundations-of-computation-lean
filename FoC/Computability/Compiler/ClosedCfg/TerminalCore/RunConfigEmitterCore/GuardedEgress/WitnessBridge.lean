import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.MetadataTokenCopy
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessLocate

set_option doc.verso true

/-!
# Metadata-witness bridge for guarded #18 egress

The tape-field pipeline has already serialized the exact final configuration
tape, but its right suffix still contains the consumed stage tape and the
guarded metadata/hit/witness tape.  The metadata copier needs a more specific
one-tape source: the selected metadata tokens lie to the left of a positive
blank gap, the exact four-bit final-hit field follows the assembled tape
field, and four additional blanks remain available for the eventual header
prepender.

This module fixes that handoff without pretending that it is a definitional
shape equality.  The finite bridge must inspect the committed branch witness:
a known witness supplies the final state, while the other witness selects the
raw state retained in the compact metadata.  Its honest output is up to
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`, because input
representatives may contain different far-edge blank padding.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessBridge

open Languages MachineDescription
open CommonGround.FiniteTransducers
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.SimulatorLayoutScanner

open MetadataTokenCopy

/-!
## Exact token currency
-/

/-- Token list for the canonical unary encoding of a natural number. -/
def natTokens : Nat -> List MetadataTokenCopy.TokenKind
  | 0 => [.done]
  | Nat.succ n => .tick :: natTokens n

/-- The two supported Boolean-cell tokens. -/
def boolToken : Bool -> MetadataTokenCopy.TokenKind
  | false => .zero
  | true => .one

/-- Token list for the canonical Boolean-word field, including its length. -/
def boolWordTokens (bits : Word Bool) : List MetadataTokenCopy.TokenKind :=
  List.append (natTokens bits.length) (bits.map boolToken)

theorem tokenBits_append
    (left right : List MetadataTokenCopy.TokenKind) :
    MetadataTokenCopy.tokenBits (List.append left right) =
      List.append (MetadataTokenCopy.tokenBits left)
        (MetadataTokenCopy.tokenBits right) := by
  induction left with
  | nil =>
      rfl
  | cons kind rest ih =>
      cases kind <;>
        unfold MetadataTokenCopy.tokenBits at ih ⊢ <;>
        unfold Languages.Word at * <;>
        simp [MetadataTokenCopy.TokenKind.bits,
          List.flatten_append]

theorem tokenBits_natTokens (n : Nat) :
    MetadataTokenCopy.tokenBits (natTokens n) = stageNatBits n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [natTokens, MetadataTokenCopy.tokenBits_cons, ih]
      simp [stageNatBits_succ, MetadataTokenCopy.TokenKind.bits]

theorem tokenBits_bool_map (bits : Word Bool) :
    MetadataTokenCopy.tokenBits (bits.map boolToken) =
      cellsCodeBits (bits.map some) := by
  induction bits with
  | nil =>
      rfl
  | cons bit rest ih =>
      cases bit <;>
        simp [boolToken, MetadataTokenCopy.tokenBits_cons,
          MetadataTokenCopy.TokenKind.bits,
          cellsCodeBits, cellCodeBits, encodeCell,
          encodeCodeWordAsInput, encodeCodeSymbolAsInput, ih]

theorem tokenBits_boolWordTokens (bits : Word Bool) :
    MetadataTokenCopy.tokenBits (boolWordTokens bits) =
      boolWordFieldBits bits [] := by
  rw [boolWordTokens, tokenBits_append,
    tokenBits_natTokens, tokenBits_bool_map]
  simp [boolWordFieldBits, cellListFieldBits]

/-- Select the final-state token block from the physical branch witness. -/
def witnessStateTokens
    (rawState : Nat) :
      LoopDispatcherDoneWitness -> List MetadataTokenCopy.TokenKind
  | .known finalState => natTokens finalState
  | .other => natTokens rawState

/-- Metadata tokens recoverable from the committed tape-2 source. -/
def sourceMetadataTokens (i : Index) :
    List MetadataTokenCopy.TokenKind :=
  List.append (boolWordTokens i.sourceLayout.input)
    (List.append (natTokens i.sourceLayout.stage)
      (witnessStateTokens i.sourceLayout.config.state
        (loopDispatcherDoneWitness i.description i.sourceLayout)))

/-- State selected by the same known/other split as
{name}`sourceMetadataTokens`. -/
def selectedState (i : Index) : Nat :=
  match loopDispatcherDoneWitness i.description i.sourceLayout with
  | .known finalState => finalState
  | .other => i.sourceLayout.config.state

theorem selectedState_eq_finalState (i : Index) :
    selectedState i = i.finalState := by
  change
    (MetadataWitnessDecoder.expected
      i.description i.sourceLayout).finalState =
      (SimulatorLayout.run i.description i.sourceLayout.stage
        i.sourceLayout).config.state
  exact MetadataWitnessDecoder.expected_finalState
    i.description i.sourceLayout

theorem witnessStateTokens_eq_selectedState (i : Index) :
    witnessStateTokens i.sourceLayout.config.state
        (loopDispatcherDoneWitness i.description i.sourceLayout) =
      natTokens (selectedState i) := by
  cases hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout <;>
    simp [witnessStateTokens, selectedState, hwitness]

theorem sourceMetadataTokens_eq_semantic (i : Index) :
    sourceMetadataTokens i =
      List.append (boolWordTokens i.fields.input)
        (List.append (natTokens i.fields.stage)
          (natTokens i.fields.config.state)) := by
  rw [sourceMetadataTokens, witnessStateTokens_eq_selectedState,
    selectedState_eq_finalState]
  rfl

theorem sourceMetadataTokenBits_eq_fields (i : Index) :
    MetadataTokenCopy.tokenBits (sourceMetadataTokens i) =
      boolWordFieldBits i.fields.input
        (List.append (stageNatBits i.fields.stage)
          (stageNatBits i.fields.config.state)) := by
  rw [sourceMetadataTokens_eq_semantic]
  rw [tokenBits_append, tokenBits_append]
  rw [tokenBits_boolWordTokens, tokenBits_natTokens,
    tokenBits_natTokens]
  simp [boolWordFieldBits, cellListFieldBits, List.append_assoc]

theorem sourceMetadataTokens_known
    (i : Index) (finalState : Nat)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState) :
    sourceMetadataTokens i =
      List.append (boolWordTokens i.sourceLayout.input)
        (List.append (natTokens i.sourceLayout.stage)
          (natTokens finalState)) := by
  simp [sourceMetadataTokens, witnessStateTokens, hwitness]

theorem sourceMetadataTokens_other
    (i : Index)
    (hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout = .other) :
    sourceMetadataTokens i =
      List.append (boolWordTokens i.sourceLayout.input)
        (List.append (natTokens i.sourceLayout.stage)
          (natTokens i.sourceLayout.config.state)) := by
  simp [sourceMetadataTokens, witnessStateTokens, hwitness]

/-!
## Exact four-bit hit tail
-/

def hitToken (i : Index) : MetadataTokenCopy.TokenKind :=
  if i.finalHit then .one else .zero

def hitBits (i : Index) : Word Bool :=
  (hitToken i).bits

theorem hitBits_eq_boolFieldBits (i : Index) :
    hitBits i = boolFieldBits i.fields.hit [] := by
  cases hhit : i.finalHit <;>
    simp [hitBits, hitToken, hhit, Index.fields,
      EgressSemantics.fieldsFromParts, boolFieldBits, cellFieldBits,
      cellCodeBits, encodeCell, encodeCodeWordAsInput,
      encodeCodeSymbolAsInput, MetadataTokenCopy.TokenKind.bits]

@[simp] theorem hitBits_length (i : Index) :
    (hitBits i).length = 4 := by
  cases hhit : i.finalHit <;>
    simp [hitBits, hitToken, hhit, MetadataTokenCopy.TokenKind.bits]

theorem hitBits_cons_false (i : Index) :
    exists tail : Word Bool, hitBits i = false :: tail := by
  cases hhit : i.finalHit
  · exact ⟨[true, false, true], by
      simp [hitBits, hitToken, hhit,
        MetadataTokenCopy.TokenKind.bits]⟩
  · exact ⟨[true, true, false], by
      simp [hitBits, hitToken, hhit,
        MetadataTokenCopy.TokenKind.bits]⟩

/-!
## Copier-ready staging shape
-/

/-- Padding choices left abstract because equivalent guarded inputs may carry
different invisible far-edge blank windows.  {lit}`gapTail + 1` makes the
required metadata/tail separator positive by construction. -/
structure ReadyLayout where
  basePadding : Nat
  gapTail : Nat
  rightPadding : Nat

def ReadyLayout.gap (layout : ReadyLayout) : Nat :=
  layout.gapTail + 1

theorem ReadyLayout.gap_pos (layout : ReadyLayout) :
    0 < layout.gap := by
  simp [ReadyLayout.gap]

/-- Exact copier source demanded from the metadata/witness bridge.  The copier
itself supplies four blanks per metadata token; the four leading blanks in
{lit}`baseLeft` are reserved for the subsequent fixed-header prepender. -/
def readyTape (i : Index) (layout : ReadyLayout) : Tape Bool :=
  MetadataTokenCopy.sourceTape
    (List.append
      (List.replicate 4 (none : Option Bool))
      (List.replicate layout.basePadding none))
    (LengthAssembly.exactTapeFieldBits i.finalTape [])
    (hitBits i)
    layout.gap
    (sourceMetadataTokens i)
    (List.replicate layout.rightPadding none)

theorem readyTape_has_positive_gap (i : Index) (layout : ReadyLayout) :
    exists gapTail,
      readyTape i layout =
        MetadataTokenCopy.sourceTape
          (List.append
            (List.replicate 4 (none : Option Bool))
            (List.replicate layout.basePadding none))
          (LengthAssembly.exactTapeFieldBits i.finalTape [])
          (hitBits i)
          (gapTail + 1)
          (sourceMetadataTokens i)
          (List.replicate layout.rightPadding none) := by
  exact ⟨layout.gapTail, rfl⟩

/-!
## Remaining finite bridge obligation
-/

/-- The known and other source branches are separate proof obligations so a
finite construction cannot silently assume that the witness always carries a
state.  Each clause accepts every tape equivalent to the serializer endpoint
and may retain only blank far-edge padding in its copier-ready representative. -/
structure Spec (bridge : MachineDescription) : Prop where
  subroutineReady : bridge.SubroutineReady
  known : forall (i : Index) (finalState : Nat),
    loopDispatcherDoneWitness i.description i.sourceLayout =
        .known finalState ->
    forall actual : Tape Bool,
      Tape.Equiv actual
          (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) ->
      exists layout : ReadyLayout,
        bridge.HaltsFromTapeEquiv actual (readyTape i layout)
  other : forall (i : Index),
    loopDispatcherDoneWitness i.description i.sourceLayout = .other ->
    forall actual : Tape Bool,
      Tape.Equiv actual
          (TapeFieldSerializer.correctedSerializedTapeFieldTarget i) ->
      exists layout : ReadyLayout,
        bridge.HaltsFromTapeEquiv actual (readyTape i layout)

theorem Spec.haltsFromTapeEquiv
    {bridge : MachineDescription} (hbridge : Spec bridge)
    (i : Index) (actual : Tape Bool)
    (hactual : Tape.Equiv actual
      (TapeFieldSerializer.correctedSerializedTapeFieldTarget i)) :
    exists layout : ReadyLayout,
      bridge.HaltsFromTapeEquiv actual (readyTape i layout) := by
  cases hwitness :
      loopDispatcherDoneWitness i.description i.sourceLayout with
  | known finalState =>
      exact hbridge.known i finalState hwitness actual hactual
  | other =>
      exact hbridge.other i hwitness actual hactual

/-- Lowest remaining production construction after the tape-field pipeline. -/
def Construction : Prop :=
  exists bridge : MachineDescription, Spec bridge

end GuardedEgress.MetadataWitnessBridge
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore

import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.OptionalCell
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFieldLocator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.PositionedRightLocator

set_option doc.verso true

/-!
# Right-first-cell editing

Finite removal and replacement of the first serialized cell in the right-side
payload of a protected exact-fuel frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Dispatch
namespace RightFirstCell

open SerializedFieldComposer
open Dispatch.RightFieldLocator

theorem encodeOptionalCodeSymbolsPayloadAppend_nil_append
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    List.append (encodeOptionalCodeSymbolsPayloadAppend cells []) suffix =
      encodeOptionalCodeSymbolsPayloadAppend cells suffix := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      simp only [encodeOptionalCodeSymbolsPayloadAppend]
      rw [← ih]
      simp [encodeOptionalCodeSymbolAppend,
        MachineDescription.encodeNatAppend, List.append_assoc]

theorem afterHeadWord_eq_rightCountPayload {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    HeadLocator.afterHeadWord L callerData =
      MachineDescription.encodeNatAppend L.right.length
        (RightPrepend.rightPayloadSuffix L callerData) := by
  unfold HeadLocator.afterHeadWord RightPrepend.rightPayloadSuffix
    optionalCellsWord encodeOptionalCodeSymbolsAppend
  rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
  rw [show
      List.append
          (MachineDescription.encodeNatAppend L.right.length
            (encodeOptionalCodeSymbolsPayloadAppend L.right []))
          (Frame.callerTag :: callerData) =
        MachineDescription.encodeNatAppend L.right.length
          (List.append
            (encodeOptionalCodeSymbolsPayloadAppend L.right [])
            (Frame.callerTag :: callerData)) by
      simp [MachineDescription.encodeNatAppend, List.append_assoc]]
  rw [encodeOptionalCodeSymbolsPayloadAppend_nil_append]

theorem rightPayloadSuffix_cons {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight) :
    RightPrepend.rightPayloadSuffix L callerData =
      List.append (optionalCellWord nextHead)
        (MoveRightNonempty.afterFirstRightCell remainingRight callerData) := by
  unfold RightPrepend.rightPayloadSuffix
    MoveRightNonempty.afterFirstRightCell
  rw [hright]
  rfl

def markedRightCountLeftRev {stateCount : Nat}
    (L : Layout stateCount) : Word MachineCodeSymbol :=
  List.append (optionalCellWord L.head).reverse
    (List.append (HeadLocator.markedCellsWord L.left).reverse
      (HeadDecoder.markedCountBaseLeftRev L))

def markedRightPayloadLeftRev {stateCount : Nat}
    (L : Layout stateCount) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat L.right.length).reverse
    (markedRightCountLeftRev L)

def rightCountSourceConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control :=
  Edits.PositionedRightLocator.config .rightCount
    (markedRightCountLeftRev L)
    (HeadLocator.afterHeadWord L callerData)

def rightPayloadGateConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control :=
  Edits.PositionedRightLocator.config .gate
    (markedRightPayloadLeftRev L)
    (RightPrepend.rightPayloadSuffix L callerData)

theorem locate_rightPayload_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    (Edits.PositionedRightLocator.machine .rightPayload).runConfigExact?
        (L.right.length + 1) (rightCountSourceConfig L callerData) =
      some (rightPayloadGateConfig L callerData) := by
  unfold rightCountSourceConfig rightPayloadGateConfig
    markedRightPayloadLeftRev
  rw [afterHeadWord_eq_rightCountPayload]
  exact Edits.PositionedRightLocator.rightCount_run_exact
    L.right.length (markedRightCountLeftRev L)
      (RightPrepend.rightPayloadSuffix L callerData)

theorem markedRightPayloadLeftRev_ne_nil {stateCount : Nat}
    (L : Layout stateCount) : markedRightPayloadLeftRev L ≠ [] := by
  intro h
  have hlength := congrArg List.length h
  simp [markedRightPayloadLeftRev, markedRightCountLeftRev,
    HeadDecoder.markedCountBaseLeftRev] at hlength

def cellDecoderSourceConfig {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Dispatch.OptionalCell.Control :=
  Dispatch.OptionalCell.sourceConfig
    (markedRightPayloadLeftRev L) nextHead
    (MoveRightNonempty.afterFirstRightCell remainingRight callerData)

def cellDecoderGateConfig {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      Dispatch.OptionalCell.Control :=
  Dispatch.OptionalCell.gateConfig
    (markedRightPayloadLeftRev L) nextHead
    (MoveRightNonempty.afterFirstRightCell remainingRight callerData)

theorem decode_firstRightCell_exact {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    Dispatch.OptionalCell.machine.runConfigExact?
        (Dispatch.OptionalCell.runSteps nextHead)
        (cellDecoderSourceConfig L nextHead remainingRight callerData) =
      some
        (cellDecoderGateConfig L nextHead remainingRight callerData) := by
  exact Dispatch.OptionalCell.run_exact
    (markedRightPayloadLeftRev L) nextHead
    (MoveRightNonempty.afterFirstRightCell remainingRight callerData)
    (markedRightPayloadLeftRev_ne_nil L)

def deleteSourceConfig {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.editConfig
    (DeleteBlock.sourceConfig nextHead
      (markedRightPayloadLeftRev L)
      (MoveRightNonempty.afterFirstRightCell remainingRight callerData))

def deleteGateConfig {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.rewindConfig
    (DeleteEndpointRewind.gateConfig
      (PhysicalBranch.deleteOutput
        (markedRightPayloadLeftRev L)
        (MoveRightNonempty.afterFirstRightCell remainingRight callerData))
      nextHead)

theorem delete_firstRightCell_exact {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine nextHead).runConfigExact?
        (DeleteRestagedMachine.runSteps nextHead
          (markedRightPayloadLeftRev L)
          (MoveRightNonempty.afterFirstRightCell remainingRight callerData))
        (deleteSourceConfig L nextHead remainingRight callerData) =
      some (deleteGateConfig L nextHead remainingRight callerData) := by
  exact DeleteRestagedMachine.run_exact nextHead
    (markedRightPayloadLeftRev L)
    (MoveRightNonempty.afterFirstRightCell remainingRight callerData)

namespace TailMachine

/-- One finite right-tail machine.  It retains the original decoded head and
the decoded first right cell while it locates and deletes that cell. -/
inductive Control where
  | count (head : Option MachineCodeSymbol)
      (inner : Edits.PositionedRightLocator.Control)
  | countReturn (head : Option MachineCodeSymbol)
  | decode (head : Option MachineCodeSymbol)
      (inner : Dispatch.OptionalCell.Control)
  | decodeReturn (head nextHead : Option MachineCodeSymbol)
  | delete (head nextHead : Option MachineCodeSymbol)
      (inner : DeleteRestagedMachine.Control)
deriving DecidableEq

namespace Control

def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite

def countFinite : Foundation.FiniteType
    (Option MachineCodeSymbol × Edits.PositionedRightLocator.Control) :=
  Foundation.FiniteType.prod optionalFinite
    Edits.PositionedRightLocator.Control.finite

def decodeFinite : Foundation.FiniteType
    (Option MachineCodeSymbol ×
      Dispatch.OptionalCell.Control) :=
  Foundation.FiniteType.prod optionalFinite
    Dispatch.OptionalCell.Control.finite

def pairFinite : Foundation.FiniteType
    (Option MachineCodeSymbol × Option MachineCodeSymbol) :=
  Foundation.FiniteType.prod optionalFinite optionalFinite

def deleteFinite : Foundation.FiniteType
    ((Option MachineCodeSymbol × Option MachineCodeSymbol) ×
      DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod pairFinite
    DeleteRestagedMachine.Control.finite

def elems : List Control :=
  List.append
    (countFinite.elems.map fun payload =>
      Control.count payload.1 payload.2)
    (List.append
      (optionalFinite.elems.map Control.countReturn)
      (List.append
        (decodeFinite.elems.map fun payload =>
          Control.decode payload.1 payload.2)
        (List.append
          (pairFinite.elems.map fun payload =>
            Control.decodeReturn payload.1 payload.2)
          (deleteFinite.elems.map fun payload =>
            Control.delete payload.1.1 payload.1.2 payload.2))))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | count head inner =>
        have h := countFinite.complete (head, inner)
        simp [elems, h]
    | countReturn head =>
        have h := optionalFinite.complete head
        simp [elems, h]
    | decode head inner =>
        have h := decodeFinite.complete (head, inner)
        simp [elems, h]
    | decodeReturn head nextHead =>
        have h := pairFinite.complete (head, nextHead)
        simp [elems, h]
    | delete head nextHead inner =>
        have h := deleteFinite.complete ((head, nextHead), inner)
        simp [elems]
        exact ⟨head, nextHead, inner, h, rfl, rfl, rfl⟩

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .count head .gate, read =>
      some (read, Direction.left, .countReturn head)
  | .count head inner, read =>
      match Edits.PositionedRightLocator.transition .rightPayload
          inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .count head target)
  | .countReturn head, read =>
      some (read, Direction.right,
        .decode head (.decode ⟨0, by decide⟩))
  | .decode head (.gate nextHead), read =>
      some (read, Direction.left, .decodeReturn head nextHead)
  | .decode head inner, read =>
      match Dispatch.OptionalCell.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .decode head target)
  | .decodeReturn head nextHead, read =>
      some (read, Direction.right,
        .delete head nextHead
          (.edit (.erase (DeleteBlock.optionalGap nextHead))))
  | .delete head nextHead inner, read =>
      match DeleteRestagedMachine.transition nextHead inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .delete head nextHead target)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .count none .rightCount
  halt := .delete none none (.rewind .gate)
  transition := transition
  statesFinite := Control.finite

def countConfig (head : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.count head) c

def decodeConfig (head : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.OptionalCell.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (Control.decode head) c

def deleteConfig (head nextHead : Option MachineCodeSymbol)
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (Control.delete head nextHead) c

theorem count_step_of_some
    (head : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control)
    (hstep :
      (Edits.PositionedRightLocator.machine .rightPayload).stepConfig c =
        some d) :
    machine.stepConfig (countConfig head c) =
      some (countConfig head d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Edits.PositionedRightLocator.machine] at hstep
      cases htransition :
          Edits.PositionedRightLocator.transition .rightPayload inner
            (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate =>
              simp [Edits.PositionedRightLocator.transition] at htransition
          | head count | rightCount | returnToCountDone =>
              simp [machine, transition, countConfig,
                TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem decode_step_of_some
    (head : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.OptionalCell.Control)
    (hstep : Dispatch.OptionalCell.machine.stepConfig c = some d) :
    machine.stepConfig (decodeConfig head c) =
      some (decodeConfig head d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Dispatch.OptionalCell.machine] at hstep
      cases htransition :
          Dispatch.OptionalCell.transition inner
            (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | gate cell =>
              simp [Dispatch.OptionalCell.transition] at htransition
          | decode count | returnLeft cell remaining | zeroBounce cell =>
              simp [machine, transition, decodeConfig,
                TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem delete_step_of_some
    (head nextHead : Option MachineCodeSymbol)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine nextHead).stepConfig c = some d) :
    machine.stepConfig (deleteConfig head nextHead c) =
      some (deleteConfig head nextHead d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [DeleteRestagedMachine.machine] at hstep
      cases htransition : DeleteRestagedMachine.transition nextHead inner
          (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          simp [machine, transition, deleteConfig,
            TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem count_run_of_some
    (head : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Edits.PositionedRightLocator.Control}
    (hrun : (Edits.PositionedRightLocator.machine .rightPayload).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (countConfig head source) =
      some (countConfig head target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.count head)
  · intro c d hstep
    simpa [countConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        count_step_of_some head c d hstep
  · simpa [countConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem decode_run_of_some
    (head : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.OptionalCell.Control}
    (hrun : Dispatch.OptionalCell.machine.runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (decodeConfig head source) =
      some (decodeConfig head target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.decode head)
  · intro c d hstep
    simpa [decodeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        decode_step_of_some head c d hstep
  · simpa [decodeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem delete_run_of_some
    (head nextHead : Option MachineCodeSymbol)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine nextHead).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (deleteConfig head nextHead source) =
      some (deleteConfig head nextHead target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.delete head nextHead)
  · intro c d hstep
    simpa [deleteConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        delete_step_of_some head nextHead c d hstep
  · simpa [deleteConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem count_decode_handoff
    (head : Option MachineCodeSymbol)
    (leftHead : MachineCodeSymbol)
    (leftTail rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (countConfig head
          (Edits.PositionedRightLocator.config .gate
            (leftHead :: leftTail) rest)) =
      some
        (decodeConfig head
          { state := Dispatch.OptionalCell.Control.decode
              ⟨0, by decide⟩
            tape := SerializedShift.cursorTape (leftHead :: leftTail) rest }) := by
  cases rest <;> rfl

theorem decode_delete_handoff
    (head nextHead : Option MachineCodeSymbol)
    (leftHead : MachineCodeSymbol)
    (leftTail rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (decodeConfig head
          { state := Dispatch.OptionalCell.Control.gate nextHead
            tape := SerializedShift.cursorTape (leftHead :: leftTail) rest }) =
      some
        (deleteConfig head nextHead
          { state := DeleteRestagedMachine.Control.edit
              (.erase (DeleteBlock.optionalGap nextHead))
            tape := SerializedShift.cursorTape (leftHead :: leftTail) rest }) := by
  cases rest <;> rfl

theorem count_decode_handoff_layout {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight) :
    machine.runConfigExact? 2
        (countConfig L.head (rightPayloadGateConfig L callerData)) =
      some
        (decodeConfig L.head
          (cellDecoderSourceConfig L nextHead remainingRight callerData)) := by
  unfold rightPayloadGateConfig cellDecoderSourceConfig
    Dispatch.OptionalCell.sourceConfig
  rw [rightPayloadSuffix_cons L nextHead remainingRight callerData hright]
  cases hleft : markedRightPayloadLeftRev L with
  | nil =>
      exact False.elim ((markedRightPayloadLeftRev_ne_nil L) hleft)
  | cons leftHead leftTail =>
      exact count_decode_handoff L.head leftHead leftTail
        (List.append (optionalCellWord nextHead)
          (MoveRightNonempty.afterFirstRightCell remainingRight callerData))

theorem decode_delete_handoff_layout {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (decodeConfig L.head
          (cellDecoderGateConfig L nextHead remainingRight callerData)) =
      some
        (deleteConfig L.head nextHead
          (deleteSourceConfig L nextHead remainingRight callerData)) := by
  unfold cellDecoderGateConfig
    Dispatch.OptionalCell.gateConfig
    deleteSourceConfig DeleteRestagedMachine.editConfig
    DeleteBlock.sourceConfig
  cases hleft : markedRightPayloadLeftRev L with
  | nil =>
      exact False.elim ((markedRightPayloadLeftRev_ne_nil L) hleft)
  | cons leftHead leftTail =>
      exact decode_delete_handoff L.head nextHead leftHead leftTail
        (List.append (optionalCellWord nextHead)
          (MoveRightNonempty.afterFirstRightCell remainingRight callerData))

def runSteps {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Nat :=
  ((((L.right.length + 1) + 2) +
      Dispatch.OptionalCell.runSteps nextHead) + 2) +
    DeleteRestagedMachine.runSteps nextHead
      (markedRightPayloadLeftRev L)
      (MoveRightNonempty.afterFirstRightCell remainingRight callerData)

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight) :
    machine.runConfigExact?
        (runSteps L nextHead remainingRight callerData)
        (countConfig L.head (rightCountSourceConfig L callerData)) =
      some
        (deleteConfig L.head nextHead
          (deleteGateConfig L nextHead remainingRight callerData)) := by
  have hcount := count_run_of_some L.head
    (locate_rightPayload_exact L callerData)
  have hcountDecode := count_decode_handoff_layout
    L nextHead remainingRight callerData hright
  have hdecode := decode_run_of_some L.head
    (decode_firstRightCell_exact L nextHead remainingRight callerData)
  have hdecodeDelete := decode_delete_handoff_layout
    L nextHead remainingRight callerData
  have hdelete := delete_run_of_some L.head nextHead
    (delete_firstRightCell_exact L nextHead remainingRight callerData)
  have hfirst := TuringMachine.runConfigExact?_trans hcount hcountDecode
  have hsecond := TuringMachine.runConfigExact?_trans hfirst hdecode
  have hthird := TuringMachine.runConfigExact?_trans hsecond hdecodeDelete
  have hfourth := TuringMachine.runConfigExact?_trans hthird hdelete
  simpa [runSteps, Nat.add_assoc] using hfourth

end TailMachine

namespace CombinedMachine

/-- Canonical-frame locator fused with the nonempty-right first-cell editor. -/
inductive Control where
  | locate (inner : OuterLocator.Control)
  | locateReturn (head : Option MachineCodeSymbol)
  | tail (inner : TailMachine.Control)
deriving DecidableEq

namespace Control

def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite

def elems : List Control :=
  List.append
    (OuterLocator.Control.elems.map Control.locate)
    (List.append
      (optionalFinite.elems.map Control.locateReturn)
      (TailMachine.Control.elems.map Control.tail))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := OuterLocator.Control.finite.complete inner
        change inner ∈ OuterLocator.Control.elems at h
        simp [elems, h]
    | locateReturn head =>
        have h := optionalFinite.complete head
        simp [elems, h]
    | tail inner =>
        have h := TailMachine.Control.finite.complete inner
        change inner ∈ TailMachine.Control.elems at h
        simp [elems, h]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate (.decode (.gate head)), read =>
      some (read, Direction.left, .locateReturn head)
  | .locate inner, read =>
      match OuterLocator.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .locate target)
  | .locateReturn head, read =>
      some (read, Direction.right,
        .tail (.count head .rightCount))
  | .tail inner, read =>
      match TailMachine.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .tail target)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate (.locate .header)
  halt := .tail (.delete none none (.rewind .gate))
  transition := transition
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      OuterLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locate c

def tailConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      TailMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.tail c

theorem locate_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol
      OuterLocator.Control)
    (hstep : OuterLocator.machine.stepConfig c = some d) :
    machine.stepConfig (locateConfig c) = some (locateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [OuterLocator.machine] at hstep
      cases htransition : OuterLocator.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          cases inner with
          | decode decoder =>
              cases decoder with
              | gate head =>
                  simp [OuterLocator.transition,
                    HeadDecoder.transition] at htransition
              | decode count =>
                  simp [machine, transition, locateConfig,
                    TuringMachine.PhaseEmbedding.liftConfig,
                    htransition]
          | locate locator | counter counter =>
              simp [machine, transition, locateConfig,
                TuringMachine.PhaseEmbedding.liftConfig, htransition]
          | locateReturn | counterReturn =>
              simp [machine, transition, locateConfig,
                TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem tail_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol
      TailMachine.Control)
    (hstep : TailMachine.machine.stepConfig c = some d) :
    machine.stepConfig (tailConfig c) = some (tailConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [TailMachine.machine] at hstep
      cases htransition : TailMachine.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          simp [machine, transition, tailConfig,
            TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem locate_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      OuterLocator.Control}
    (hrun : OuterLocator.machine.runConfigExact? steps source = some target) :
    machine.runConfigExact? steps (locateConfig source) =
      some (locateConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.locate
  · intro c d hstep
    simpa [locateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        locate_step_of_some c d hstep
  · simpa [locateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem tail_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      TailMachine.Control}
    (hrun : TailMachine.machine.runConfigExact? steps source = some target) :
    machine.runConfigExact? steps (tailConfig source) =
      some (tailConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.tail
  · intro c d hstep
    simpa [tailConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        tail_step_of_some c d hstep
  · simpa [tailConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem handoff
    (head : Option MachineCodeSymbol)
    (leftHead : MachineCodeSymbol)
    (leftTail rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (locateConfig
          { state := OuterLocator.Control.decode
              (.gate head)
            tape := SerializedShift.cursorTape (leftHead :: leftTail) rest }) =
      some
        (tailConfig
          { state := TailMachine.Control.count head .rightCount
            tape := SerializedShift.cursorTape (leftHead :: leftTail) rest }) := by
  cases rest <;> rfl

theorem handoff_layout {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (locateConfig
          (OuterLocator.decodeConfig
            (HeadDecoder.rightCountConfig L callerData))) =
      some
        (tailConfig
          (TailMachine.countConfig L.head
            (rightCountSourceConfig L callerData))) := by
  change
    machine.runConfigExact? 2
        (locateConfig
          { state := OuterLocator.Control.decode (.gate L.head)
            tape := SerializedShift.cursorTape
              (markedRightCountLeftRev L)
              (HeadLocator.afterHeadWord L callerData) }) =
      some
        (tailConfig
          { state := TailMachine.Control.count L.head .rightCount
            tape := SerializedShift.cursorTape
              (markedRightCountLeftRev L)
              (HeadLocator.afterHeadWord L callerData) })
  cases hleft : markedRightCountLeftRev L with
  | nil =>
      have hne : markedRightCountLeftRev L ≠ [] := by
        intro h
        have hlength := congrArg List.length h
        simp [markedRightCountLeftRev,
          HeadDecoder.markedCountBaseLeftRev] at hlength
      exact False.elim (hne hleft)
  | cons leftHead leftTail =>
      exact handoff L.head leftHead leftTail
        (HeadLocator.afterHeadWord L callerData)

def runSteps {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Nat :=
  (OuterLocator.runSteps L + 2) +
    TailMachine.runSteps L nextHead remainingRight callerData

/-- One exact finite run from the canonical protected frame through the first
right-cell deletion.  The marked prefix is intentionally left for the next
restoration/count-correction phase. -/
theorem run_exact {stateCount : Nat}
    (L : Layout stateCount)
    (nextHead : Option MachineCodeSymbol)
    (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hright : L.right = nextHead :: remainingRight) :
    machine.runConfigExact?
        (runSteps L nextHead remainingRight callerData)
        (locateConfig
          (OuterLocator.locateConfig
            (FieldLocator.startConfig L callerData))) =
      some
        (tailConfig
          (TailMachine.deleteConfig L.head nextHead
            (deleteGateConfig L nextHead remainingRight callerData))) := by
  have hlocate := locate_run_of_some
    (OuterLocator.run_exact L callerData)
  have hhandoff := handoff_layout L callerData
  have htail := tail_run_of_some
    (TailMachine.run_exact L nextHead remainingRight callerData hright)
  have hpref := TuringMachine.runConfigExact?_trans hlocate hhandoff
  have hrun := TuringMachine.runConfigExact?_trans hpref htail
  simpa [runSteps, Nat.add_assoc] using hrun

end CombinedMachine

end RightFirstCell
end Dispatch
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

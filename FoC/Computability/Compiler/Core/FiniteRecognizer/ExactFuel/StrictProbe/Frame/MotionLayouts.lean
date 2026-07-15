import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.EditBlocks
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
namespace HeadReplacement
def replaceHead {stateCount : Nat} (L : Layout stateCount) (newHead : Option MachineCodeSymbol) : Layout stateCount :=
  { L with head := newHead }
def replacementWord {stateCount : Nat} (L : Layout stateCount) (newHead : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (headPrefix L) (List.append (optionalCellWord newHead) (HeadLocator.afterHeadWord L callerData))
theorem protectedWord_head_decomp {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Frame.protectedWord L callerData = List.append (headPrefix L)
        (List.append (optionalCellWord L.head) (HeadLocator.afterHeadWord L callerData)) := by
  rw [protectedWord_eq_headPrefix_headSuffix]
  rfl
theorem replacementWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (newHead : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    replacementWord L newHead callerData = Frame.protectedWord (replaceHead L newHead) callerData := by
  rw [protectedWord_eq_headPrefix_headSuffix]
  rfl
end HeadReplacement
namespace RightPrepend
def rightCountPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := List.append (headPrefix L) (optionalCellWord L.head)
def rightPayloadPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := List.append (rightCountPrefix L) (MachineDescription.encodeNat L.right.length)
def rightPayloadSuffix {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  HeadLocator.cellsPayloadAppend L.right (Frame.callerTag :: callerData)
theorem protectedWord_decomp {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData = List.append (rightPayloadPrefix L) (rightPayloadSuffix L callerData) := by
  have hright := encodeOptionalCodeSymbolsPayloadAppend_eq_append L.right (Frame.callerTag :: callerData)
  rw [protectedWord_eq_headPrefix_headSuffix]
  unfold rightPayloadPrefix rightCountPrefix rightPayloadSuffix headSuffix
  rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend, hright]
  simp [optionalCellsWord, encodeOptionalCodeSymbolsAppend, MachineDescription.encodeNatAppend, List.append_assoc]
def afterWriteWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (rightPayloadPrefix L) (List.append (optionalCellWord write) (rightPayloadSuffix L callerData))
def rightCountTicksPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := List.append (rightCountPrefix L) (HeadLocator.ticks L.right.length)
def afterCountDoneSuffix {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done :: List.append (optionalCellWord write) (rightPayloadSuffix L callerData)
def afterIncrementWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (rightCountTicksPrefix L) (MachineCodeSymbol.tick :: afterCountDoneSuffix L write callerData)
def prependedRightLayout {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) : Layout stateCount :=
  { L with right := write :: L.right }
theorem rightCountPrefix_prepended {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) :
    rightCountPrefix (prependedRightLayout L write) = rightCountPrefix L := by
  cases L
  rfl
theorem rightPayloadSuffix_prepended {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    rightPayloadSuffix (prependedRightLayout L write) callerData = List.append (optionalCellWord write) (rightPayloadSuffix L callerData) := by
  cases L with
  | mk fuel state left head right =>
      unfold rightPayloadSuffix prependedRightLayout
      rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
      rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
      simp [encodeOptionalCodeSymbolsPayloadAppend, optionalCellWord, encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend]
theorem afterIncrementWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    afterIncrementWord L write callerData = Frame.protectedWord (prependedRightLayout L write) callerData := by
  rw [protectedWord_decomp]
  unfold rightPayloadPrefix
  rw [rightCountPrefix_prepended, rightPayloadSuffix_prepended]
  unfold afterIncrementWord rightCountTicksPrefix afterCountDoneSuffix
  have hlength : (prependedRightLayout L write).right.length = L.right.length + 1 := by
    cases L
    rfl
  rw [hlength]
  rw [show MachineDescription.encodeNat (L.right.length + 1) = MachineCodeSymbol.tick :: MachineDescription.encodeNat L.right.length by rfl]
  rw [HeadLocator.encodeNat_eq_ticks_done]
  have hticks := HeadLocator.ticks_append_tick L.right.length (MachineCodeSymbol.done :: List.append (optionalCellWord write) (rightPayloadSuffix L callerData))
  have hprefix := congrArg (fun suffix : Word MachineCodeSymbol =>
      List.append (rightCountPrefix L) suffix) hticks
  calc
    List.append (List.append (rightCountPrefix L) (HeadLocator.ticks L.right.length))
        (MachineCodeSymbol.tick :: MachineCodeSymbol.done :: List.append (optionalCellWord write) (rightPayloadSuffix L callerData)) =
      List.append (rightCountPrefix L) (List.append (HeadLocator.ticks L.right.length) (MachineCodeSymbol.tick :: MachineCodeSymbol.done :: List.append (optionalCellWord write)
              (rightPayloadSuffix L callerData))) := by
        exact List.append_assoc _ _ _
    _ = List.append (rightCountPrefix L) (MachineCodeSymbol.tick :: List.append (HeadLocator.ticks L.right.length) (MachineCodeSymbol.done ::
              List.append (optionalCellWord write) (rightPayloadSuffix L callerData))) := hprefix
    _ = List.append (List.append (rightCountPrefix L) (MachineCodeSymbol.tick :: List.append (HeadLocator.ticks L.right.length) [MachineCodeSymbol.done]))
        (List.append (optionalCellWord write) (rightPayloadSuffix L callerData)) := by simp [List.append_assoc]
end RightPrepend
namespace MoveLeftNonempty
def leftPayloadPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel
      (MachineDescription.encodeNatAppend L.state.val (MachineDescription.encodeNat L.left.length))
def afterFirstLeftCell {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  HeadLocator.cellsPayloadAppend remainingLeft (encodeOptionalCodeSymbolAppend L.head (encodeOptionalCodeSymbolsAppend L.right (Frame.callerTag :: callerData)))
def afterDeleteWord {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (leftPayloadPrefix L) (afterFirstLeftCell L remainingLeft callerData)
def leftCountPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNat L.state.val)
def afterCountTick {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend remainingLeft.length (HeadLocator.cellsPayloadAppend remainingLeft
      (encodeOptionalCodeSymbolAppend L.head (encodeOptionalCodeSymbolsAppend L.right (Frame.callerTag :: callerData))))
def countCorrectedWord {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (leftCountPrefix L) (afterCountTick L remainingLeft callerData)
theorem afterDeleteWord_count_decomp {stateCount : Nat} (L : Layout stateCount) (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol)
    (hleft : L.left = nextHead :: remainingLeft) :
    afterDeleteWord L remainingLeft callerData = List.append (leftCountPrefix L) (MachineCodeSymbol.tick :: afterCountTick L remainingLeft callerData) := by
  unfold afterDeleteWord leftPayloadPrefix leftCountPrefix afterCountTick afterFirstLeftCell
  rw [hleft]
  simp [MachineDescription.encodeNatAppend, MachineDescription.encodeNat, List.append_assoc]
def removedLeftLayout {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol)) : Layout stateCount :=
  { L with left := remainingLeft }
theorem countCorrectedWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (remainingLeft : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) :
    countCorrectedWord L remainingLeft callerData = Frame.protectedWord (removedLeftLayout L remainingLeft) callerData := by
  cases L with
  | mk fuel state left head right =>
      unfold countCorrectedWord leftCountPrefix afterCountTick removedLeftLayout Frame.protectedWord Layout.encodeAppend
      rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
      simp [encodeOptionalCodeSymbolsAppend, MachineDescription.encodeNatAppend, List.append_assoc]
def headReplacedLayout {stateCount : Nat} (L : Layout stateCount) (nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol)) : Layout stateCount :=
  HeadReplacement.replaceHead (removedLeftLayout L remainingLeft) nextHead
def reshapedLayout {stateCount : Nat} (L : Layout stateCount) (write nextHead : Option MachineCodeSymbol) (remainingLeft : List (Option MachineCodeSymbol)) : Layout stateCount :=
  RightPrepend.prependedRightLayout (headReplacedLayout L nextHead remainingLeft) write
end MoveLeftNonempty
namespace MoveLeftEmpty
def blankedHeadLayout {stateCount : Nat} (L : Layout stateCount) : Layout stateCount := HeadReplacement.replaceHead L none
def reshapedLayout {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) : Layout stateCount :=
  RightPrepend.prependedRightLayout (blankedHeadLayout L) write
theorem reshapedLayout_eq_moveLeftTarget {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (hleft : L.left = []) :
    reshapedLayout L write = HeadActionShape.moveLeftTarget L.fuel write L.state L := by
  cases L with
  | mk fuel state left head right =>
      simp only at hleft
      subst left
      rfl
end MoveLeftEmpty
namespace LeftPrepend
def leftCountPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: MachineDescription.encodeNatAppend L.fuel (MachineDescription.encodeNat L.state.val)
def leftPayloadPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := List.append (leftCountPrefix L) (MachineDescription.encodeNat L.left.length)
def leftPayloadSuffix {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  HeadLocator.cellsPayloadAppend L.left (encodeOptionalCodeSymbolAppend L.head (encodeOptionalCodeSymbolsAppend L.right (Frame.callerTag :: callerData)))
theorem protectedWord_decomp {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData = List.append (leftPayloadPrefix L) (leftPayloadSuffix L callerData) := by
  cases L with
  | mk fuel state left head right =>
      unfold leftPayloadPrefix leftCountPrefix leftPayloadSuffix Frame.protectedWord Layout.encodeAppend
      rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
      simp [encodeOptionalCodeSymbolsAppend, MachineDescription.encodeNatAppend, List.append_assoc]
def afterWriteWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (leftPayloadPrefix L) (List.append (optionalCellWord write) (leftPayloadSuffix L callerData))
def leftCountTicksPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := List.append (leftCountPrefix L) (HeadLocator.ticks L.left.length)
def afterCountDoneSuffix {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done :: List.append (optionalCellWord write) (leftPayloadSuffix L callerData)
def afterIncrementWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (leftCountTicksPrefix L) (MachineCodeSymbol.tick :: afterCountDoneSuffix L write callerData)
def prependedLeftLayout {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) : Layout stateCount :=
  { L with left := write :: L.left }
theorem leftCountPrefix_prepended {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) :
    leftCountPrefix (prependedLeftLayout L write) = leftCountPrefix L := by
  cases L
  rfl
theorem leftPayloadSuffix_prepended {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    leftPayloadSuffix (prependedLeftLayout L write) callerData = List.append (optionalCellWord write) (leftPayloadSuffix L callerData) := by
  cases L with
  | mk fuel state left head right =>
      unfold leftPayloadSuffix prependedLeftLayout
      rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
      rw [HeadLocator.cellsPayloadAppend_eq_encodePayloadAppend]
      simp [encodeOptionalCodeSymbolsPayloadAppend, optionalCellWord, encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend]
theorem afterIncrementWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (callerData : Word MachineCodeSymbol) :
    afterIncrementWord L write callerData = Frame.protectedWord (prependedLeftLayout L write) callerData := by
  rw [protectedWord_decomp]
  unfold leftPayloadPrefix
  rw [leftCountPrefix_prepended, leftPayloadSuffix_prepended]
  unfold afterIncrementWord leftCountTicksPrefix afterCountDoneSuffix
  have hlength : (prependedLeftLayout L write).left.length = L.left.length + 1 := by
    cases L
    rfl
  rw [hlength]
  rw [show MachineDescription.encodeNat (L.left.length + 1) = MachineCodeSymbol.tick :: MachineDescription.encodeNat L.left.length by rfl]
  rw [HeadLocator.encodeNat_eq_ticks_done]
  have hticks := HeadLocator.ticks_append_tick L.left.length (MachineCodeSymbol.done :: List.append (optionalCellWord write) (leftPayloadSuffix L callerData))
  have hprefix := congrArg (fun suffix : Word MachineCodeSymbol =>
      List.append (leftCountPrefix L) suffix) hticks
  calc
    List.append (List.append (leftCountPrefix L) (HeadLocator.ticks L.left.length))
        (MachineCodeSymbol.tick :: MachineCodeSymbol.done :: List.append (optionalCellWord write) (leftPayloadSuffix L callerData)) =
      List.append (leftCountPrefix L) (List.append (HeadLocator.ticks L.left.length)
          (MachineCodeSymbol.tick :: MachineCodeSymbol.done :: List.append (optionalCellWord write) (leftPayloadSuffix L callerData))) := by
        exact List.append_assoc _ _ _
    _ = List.append (leftCountPrefix L) (MachineCodeSymbol.tick :: List.append (HeadLocator.ticks L.left.length) (MachineCodeSymbol.done ::
              List.append (optionalCellWord write) (leftPayloadSuffix L callerData))) := hprefix
    _ = List.append (List.append (leftCountPrefix L) (MachineCodeSymbol.tick :: List.append (HeadLocator.ticks L.left.length) [MachineCodeSymbol.done]))
        (List.append (optionalCellWord write) (leftPayloadSuffix L callerData)) := by simp [List.append_assoc]
end LeftPrepend
namespace MoveRightNonempty
def afterFirstRightCell (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  HeadLocator.cellsPayloadAppend remainingRight (Frame.callerTag :: callerData)
def afterCountTick (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend remainingRight.length (afterFirstRightCell remainingRight callerData)
def countCorrectedWord {stateCount : Nat} (L : Layout stateCount) (remainingRight : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (RightPrepend.rightCountPrefix L) (afterCountTick remainingRight callerData)
def removedRightLayout {stateCount : Nat} (L : Layout stateCount) (remainingRight : List (Option MachineCodeSymbol)) : Layout stateCount :=
  { L with right := remainingRight }
theorem countCorrectedWord_eq_protectedWord {stateCount : Nat} (L : Layout stateCount) (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) :
    countCorrectedWord L remainingRight callerData = Frame.protectedWord (removedRightLayout L remainingRight) callerData := by
  have hprefix : RightPrepend.rightCountPrefix (removedRightLayout L remainingRight) = RightPrepend.rightCountPrefix L := by
    cases L
    rfl
  have hsuffix : RightPrepend.rightPayloadSuffix (removedRightLayout L remainingRight) callerData = afterFirstRightCell remainingRight callerData := by
    cases L
    rfl
  have hlength : (removedRightLayout L remainingRight).right.length = remainingRight.length := by
    cases L
    rfl
  rw [RightPrepend.protectedWord_decomp]
  unfold countCorrectedWord afterCountTick RightPrepend.rightPayloadPrefix
  rw [hprefix, hsuffix, hlength]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]
def headReplacedLayout {stateCount : Nat} (L : Layout stateCount) (nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol)) : Layout stateCount :=
  HeadReplacement.replaceHead (removedRightLayout L remainingRight) nextHead
def reshapedLayout {stateCount : Nat} (L : Layout stateCount) (write nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol)) : Layout stateCount :=
  LeftPrepend.prependedLeftLayout (headReplacedLayout L nextHead remainingRight) write
theorem reshapedLayout_eq_moveRightTarget {stateCount : Nat} (L : Layout stateCount) (write nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol))
    (hright : L.right = nextHead :: remainingRight) :
    reshapedLayout L write nextHead remainingRight = HeadActionShape.moveRightTarget L.fuel write L.state L := by
  cases L with
  | mk fuel state left head right =>
      simp only at hright
      subst right
      rfl
end MoveRightNonempty
namespace MoveRightEmpty
def blankedHeadLayout {stateCount : Nat} (L : Layout stateCount) : Layout stateCount := HeadReplacement.replaceHead L none
def reshapedLayout {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) : Layout stateCount := LeftPrepend.prependedLeftLayout (blankedHeadLayout L) write
theorem reshapedLayout_eq_moveRightTarget {stateCount : Nat} (L : Layout stateCount) (write : Option MachineCodeSymbol) (hright : L.right = []) :
    reshapedLayout L write = HeadActionShape.moveRightTarget L.fuel write L.state L := by
  cases L with
  | mk fuel state left head right =>
      simp only at hright
      subst right
      rfl
end MoveRightEmpty
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer

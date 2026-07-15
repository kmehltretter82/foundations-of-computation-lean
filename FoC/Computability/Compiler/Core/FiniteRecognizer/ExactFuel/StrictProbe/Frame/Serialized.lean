import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.SerializedShift
namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer
open Languages
def optionalCellWord (cell : Option MachineCodeSymbol) : Word MachineCodeSymbol := encodeOptionalCodeSymbolAppend cell []
def optionalCellsWord (cells : List (Option MachineCodeSymbol)) : Word MachineCodeSymbol := encodeOptionalCodeSymbolsAppend cells []
def afterStateWord {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeOptionalCodeSymbolsAppend L.left (encodeOptionalCodeSymbolAppend L.head (encodeOptionalCodeSymbolsAppend L.right (Frame.callerTag :: callerData)))
def stateSuffix {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend L.state.val (afterStateWord L callerData)
def statePrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := MachineCodeSymbol.header :: MachineDescription.encodeNat L.fuel
def headPrefix {stateCount : Nat} (L : Layout stateCount) : Word MachineCodeSymbol := List.append (statePrefix L)
    (List.append (MachineDescription.encodeNat L.state.val) (optionalCellsWord L.left))
def headSuffix {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (optionalCellWord L.head) (List.append (optionalCellsWord L.right) (Frame.callerTag :: callerData))
theorem encodeOptionalCodeSymbolAppend_eq_append (cell : Option MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolAppend cell suffix = List.append (optionalCellWord cell) suffix := by
  simp [optionalCellWord, encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend]
theorem encodeOptionalCodeSymbolsPayloadAppend_eq_append (cells : List (Option MachineCodeSymbol)) (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolsPayloadAppend cells suffix = List.append (encodeOptionalCodeSymbolsPayloadAppend cells []) suffix := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [encodeOptionalCodeSymbolsPayloadAppend]
      rw [ih]
      simp [encodeOptionalCodeSymbolAppend, MachineDescription.encodeNatAppend, List.append_assoc]
theorem encodeOptionalCodeSymbolsAppend_eq_append (cells : List (Option MachineCodeSymbol)) (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolsAppend cells suffix = List.append (optionalCellsWord cells) suffix := by
  simp only [optionalCellsWord, encodeOptionalCodeSymbolsAppend]
  rw [encodeOptionalCodeSymbolsPayloadAppend_eq_append]
  simp [MachineDescription.encodeNatAppend, List.append_assoc]
theorem protectedWord_eq_statePrefix_stateSuffix {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData = List.append (statePrefix L) (stateSuffix L callerData) := by
  simp [Frame.protectedWord, Layout.encodeAppend, statePrefix, stateSuffix, afterStateWord, MachineDescription.encodeNatAppend]
theorem protectedWord_eq_headPrefix_headSuffix {stateCount : Nat} (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData = List.append (headPrefix L) (headSuffix L callerData) := by
  simp only [Frame.protectedWord, Layout.encodeAppend, headPrefix, headSuffix, statePrefix, optionalCellWord, optionalCellsWord]
  rw [encodeOptionalCodeSymbolsAppend_eq_append, encodeOptionalCodeSymbolAppend_eq_append]
  rw [encodeOptionalCodeSymbolsAppend_eq_append]
  simp [optionalCellWord, optionalCellsWord, MachineDescription.encodeNatAppend, List.append_assoc]
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer

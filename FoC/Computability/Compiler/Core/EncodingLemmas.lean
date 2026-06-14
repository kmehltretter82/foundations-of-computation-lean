import FoC.Computability.Compiler.Core.TapeCodePrimitives

set_option doc.verso true

/-!
# Shared encoding append lemmas

These small algebraic facts keep finite-machine proofs from depending on a
particular scanner module just to reassociate structured code-word encodings.
-/

namespace FoC
namespace Computability

open Languages

theorem encodeNatAppend_append
    (n : Nat) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend n (List.append suffix tail) =
      List.append (MachineDescription.encodeNatAppend n suffix) tail := by
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

theorem encodeCellAppend_append
    (cell : Option Bool) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeCellAppend cell (List.append suffix tail) =
      List.append (MachineDescription.encodeCellAppend cell suffix) tail := by
  cases cell with
  | none =>
      simp [MachineDescription.encodeCellAppend, MachineDescription.encodeCell]
  | some b =>
      cases b <;>
        simp [MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell]

theorem encodeBoolAppend_append
    (b : Bool) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeBoolAppend b (List.append suffix tail) =
      List.append (MachineDescription.encodeBoolAppend b suffix) tail := by
  cases b <;>
    simp [MachineDescription.encodeBoolAppend,
      MachineDescription.encodeCellAppend, MachineDescription.encodeCell]

theorem encodeCellsAppend_append
    (cells : List (Option Bool)) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeCellsAppend cells (List.append suffix tail) =
      List.append (MachineDescription.encodeCellsAppend cells suffix)
        tail := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [MachineDescription.encodeCellsAppend,
        MachineDescription.encodeCellAppend]
      change
        List.append (MachineDescription.encodeCell cell)
          (MachineDescription.encodeCellsAppend rest
            (List.append suffix tail)) =
        List.append (MachineDescription.encodeCell cell)
          (List.append (MachineDescription.encodeCellsAppend rest suffix)
            tail)
      rw [ih]

theorem encodeCellListAppend_append
    (cells : List (Option Bool)) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeCellListAppend cells (List.append suffix tail) =
      List.append (MachineDescription.encodeCellListAppend cells suffix)
        tail := by
  simp [MachineDescription.encodeCellListAppend]
  change
    MachineDescription.encodeNatAppend cells.length
        (MachineDescription.encodeCellsAppend cells
          (List.append suffix tail)) =
      List.append
        (MachineDescription.encodeNatAppend cells.length
          (MachineDescription.encodeCellsAppend cells suffix))
        tail
  rw [encodeCellsAppend_append]
  rw [encodeNatAppend_append]

theorem encodeBoolWordAppend_append
    (w : Word Bool) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeBoolWordAppend w (List.append suffix tail) =
      List.append (MachineDescription.encodeBoolWordAppend w suffix)
        tail := by
  simpa [MachineDescription.encodeBoolWordAppend] using
    encodeCellListAppend_append (w.map some) suffix tail

theorem encodeTapeAppend_append
    (T : Tape Bool) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeTapeAppend T (List.append suffix tail) =
      List.append (MachineDescription.encodeTapeAppend T suffix) tail := by
  cases T with
  | mk left head right =>
      simp [MachineDescription.encodeTapeAppend]
      change
        MachineDescription.encodeCellListAppend left
            (MachineDescription.encodeCellAppend head
              (MachineDescription.encodeCellListAppend right
                (List.append suffix tail))) =
          List.append
            (MachineDescription.encodeCellListAppend left
              (MachineDescription.encodeCellAppend head
                (MachineDescription.encodeCellListAppend right suffix)))
            tail
      rw [encodeCellListAppend_append right suffix tail]
      rw [encodeCellAppend_append head
        (MachineDescription.encodeCellListAppend right suffix) tail]
      rw [encodeCellListAppend_append left
        (MachineDescription.encodeCellAppend head
          (MachineDescription.encodeCellListAppend right suffix)) tail]

theorem encodeConfigurationAppend_append
    (c : MachineDescription.Configuration)
    (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeConfigurationAppend c
        (List.append suffix tail) =
      List.append
        (MachineDescription.encodeConfigurationAppend c suffix) tail := by
  cases c with
  | mk state tape =>
      simp [MachineDescription.encodeConfigurationAppend]
      change
        MachineDescription.encodeNatAppend state
            (MachineDescription.encodeTapeAppend tape
              (List.append suffix tail)) =
          List.append
            (MachineDescription.encodeNatAppend state
              (MachineDescription.encodeTapeAppend tape suffix))
            tail
      rw [encodeTapeAppend_append tape suffix tail]
      rw [encodeNatAppend_append state
        (MachineDescription.encodeTapeAppend tape suffix) tail]

theorem encodeCodeWordAsInput_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeBoolWordAppend w suffix) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWord w))
        (MachineDescription.encodeCodeWordAsInput suffix) := by
  have h :=
    encodeBoolWordAppend_append w ([] : Word MachineCodeSymbol) suffix
  simp at h
  rw [h]
  change
    MachineDescription.encodeCodeWordAsInput
        (List.append (MachineDescription.encodeBoolWordAppend w []) suffix) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWord w))
        (MachineDescription.encodeCodeWordAsInput suffix)
  rw [MachineDescription.encodeCodeWordAsInput_append]
  rfl

end Computability
end FoC

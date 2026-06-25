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

/-!
## Decoder-backed cancellation

The structured encoders below are self-delimiting: decoding an encoded prefix
returns both the payload and the unconsumed suffix.  These lemmas package the
standard proof pattern "decode both sides, then compare the returned pairs".
They are intentionally not provided for raw {name}`MachineDescription.encodeCellsAppend`,
whose split between payload cells and suffix is not unique without the
length-prefixed wrapper.
-/

theorem encodeNatAppend_inj
    {n m : Nat}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeNatAppend n suffix =
        MachineDescription.encodeNatAppend m tail) :
    n = m ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeNat
          (MachineDescription.encodeNatAppend n suffix) =
        MachineDescription.decodeNat
          (MachineDescription.encodeNatAppend m tail) := by
    rw [h]
  have hpair : (n, suffix) = (m, tail) := by
    simpa [MachineDescription.decodeNat_encodeNatAppend] using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeCellAppend_inj
    {cell other : Option Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeCellAppend cell suffix =
        MachineDescription.encodeCellAppend other tail) :
    cell = other ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeCell
          (MachineDescription.encodeCellAppend cell suffix) =
        MachineDescription.decodeCell
          (MachineDescription.encodeCellAppend other tail) := by
    rw [h]
  have hpair : (cell, suffix) = (other, tail) := by
    simpa [MachineDescription.decodeCell_encodeCellAppend] using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeBoolAppend_inj
    {b c : Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeBoolAppend b suffix =
        MachineDescription.encodeBoolAppend c tail) :
    b = c ∧ suffix = tail := by
  simpa [MachineDescription.encodeBoolAppend] using
    encodeCellAppend_inj h

theorem encodeDirectionAppend_inj
    {dir other : Direction}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeDirectionAppend dir suffix =
        MachineDescription.encodeDirectionAppend other tail) :
    dir = other ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeDirection
          (MachineDescription.encodeDirectionAppend dir suffix) =
        MachineDescription.decodeDirection
          (MachineDescription.encodeDirectionAppend other tail) := by
    rw [h]
  have hpair : (dir, suffix) = (other, tail) := by
    simpa [MachineDescription.decodeDirection_encodeDirectionAppend] using
      hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeCellListAppend_inj
    {cells other : List (Option Bool)}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeCellListAppend cells suffix =
        MachineDescription.encodeCellListAppend other tail) :
    cells = other ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeCellList
          (MachineDescription.encodeCellListAppend cells suffix) =
        MachineDescription.decodeCellList
          (MachineDescription.encodeCellListAppend other tail) := by
    rw [h]
  have hpair : (cells, suffix) = (other, tail) := by
    simpa [MachineDescription.decodeCellList_encodeCellListAppend] using
      hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeBoolWordAppend_inj
    {w v : Word Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeBoolWordAppend w suffix =
        MachineDescription.encodeBoolWordAppend v tail) :
    w = v ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeBoolWord
          (MachineDescription.encodeBoolWordAppend w suffix) =
        MachineDescription.decodeBoolWord
          (MachineDescription.encodeBoolWordAppend v tail) := by
    rw [h]
  have hpair : (w, suffix) = (v, tail) := by
    simpa [MachineDescription.decodeBoolWord_encodeBoolWordAppend] using
      hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeTapeAppend_inj
    {T U : Tape Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeTapeAppend T suffix =
        MachineDescription.encodeTapeAppend U tail) :
    T = U ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeTape
          (MachineDescription.encodeTapeAppend T suffix) =
        MachineDescription.decodeTape
          (MachineDescription.encodeTapeAppend U tail) := by
    rw [h]
  have hpair : (T, suffix) = (U, tail) := by
    simpa [MachineDescription.decodeTape_encodeTapeAppend] using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeConfigurationAppend_inj
    {c d : MachineDescription.Configuration}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeConfigurationAppend c suffix =
        MachineDescription.encodeConfigurationAppend d tail) :
    c = d ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeConfiguration
          (MachineDescription.encodeConfigurationAppend c suffix) =
        MachineDescription.decodeConfiguration
          (MachineDescription.encodeConfigurationAppend d tail) := by
    rw [h]
  have hpair : (c, suffix) = (d, tail) := by
    simpa [MachineDescription.decodeConfiguration_encodeConfigurationAppend]
      using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeTransitionAppend_inj
    {t u : TransitionDescription}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeTransitionAppend t suffix =
        MachineDescription.encodeTransitionAppend u tail) :
    t = u ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeTransition
          (MachineDescription.encodeTransitionAppend t suffix) =
        MachineDescription.decodeTransition
          (MachineDescription.encodeTransitionAppend u tail) := by
    rw [h]
  have hpair : (t, suffix) = (u, tail) := by
    simpa [MachineDescription.decodeTransition_encodeTransition_append]
      using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeDescriptionAppend_inj
    {D E : MachineDescription}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      MachineDescription.encodeDescriptionAppend D suffix =
        MachineDescription.encodeDescriptionAppend E tail) :
    D = E ∧ suffix = tail := by
  have hdecode :
      MachineDescription.decodeDescriptionPrefix
          (MachineDescription.encodeDescriptionAppend D suffix) =
        MachineDescription.decodeDescriptionPrefix
          (MachineDescription.encodeDescriptionAppend E tail) := by
    rw [h]
  have hpair : (D, suffix) = (E, tail) := by
    simpa [MachineDescription.decodeDescriptionPrefix_encodeDescriptionAppend]
      using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end Computability
end FoC

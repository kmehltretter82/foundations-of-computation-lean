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
open MachineDescription

theorem encodeNatAppend_append
    (n : Nat) (suffix tail : Word MachineCodeSymbol) :
    encodeNatAppend n (List.append suffix tail) =
      List.append (encodeNatAppend n suffix) tail := by
  simp [encodeNatAppend, List.append_assoc]

theorem encodeCellAppend_append
    (cell : Option Bool) (suffix tail : Word MachineCodeSymbol) :
    encodeCellAppend cell (List.append suffix tail) =
      List.append (encodeCellAppend cell suffix) tail := by
  cases cell with
  | none =>
      simp [encodeCellAppend, encodeCell]
  | some b =>
      cases b <;>
        simp [encodeCellAppend,
          encodeCell]

theorem encodeBoolAppend_append
    (b : Bool) (suffix tail : Word MachineCodeSymbol) :
    encodeBoolAppend b (List.append suffix tail) =
      List.append (encodeBoolAppend b suffix) tail := by
  cases b <;>
    simp [encodeBoolAppend,
      encodeCellAppend, encodeCell]

theorem encodeCellsAppend_append
    (cells : List (Option Bool)) (suffix tail : Word MachineCodeSymbol) :
    encodeCellsAppend cells (List.append suffix tail) =
      List.append (encodeCellsAppend cells suffix)
        tail := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [encodeCellsAppend,
        encodeCellAppend]
      change
        List.append (encodeCell cell)
          (encodeCellsAppend rest
            (List.append suffix tail)) =
        List.append (encodeCell cell)
          (List.append (encodeCellsAppend rest suffix)
            tail)
      rw [ih]

theorem encodeCellListAppend_append
    (cells : List (Option Bool)) (suffix tail : Word MachineCodeSymbol) :
    encodeCellListAppend cells (List.append suffix tail) =
      List.append (encodeCellListAppend cells suffix)
        tail := by
  simp [encodeCellListAppend]
  change
    encodeNatAppend cells.length
        (encodeCellsAppend cells
          (List.append suffix tail)) =
      List.append
        (encodeNatAppend cells.length
          (encodeCellsAppend cells suffix))
        tail
  rw [encodeCellsAppend_append]
  rw [encodeNatAppend_append]

theorem encodeBoolWordAppend_append
    (w : Word Bool) (suffix tail : Word MachineCodeSymbol) :
    encodeBoolWordAppend w (List.append suffix tail) =
      List.append (encodeBoolWordAppend w suffix)
        tail := by
  simpa [encodeBoolWordAppend] using
    encodeCellListAppend_append (w.map some) suffix tail

theorem dovetailControllerLayout_encode_eq_header_stageInput_append_result
    (C : DovetailControllerLayout) :
    DovetailControllerLayout.encode C =
      MachineCodeSymbol.header ::
        List.append (PairedRecognizerDovetailControllerStageInputCode C)
          (encodeBoolWordAppend C.result []) := by
  cases C with
  | mk input stage result =>
      have hnat :
          encodeNatAppend stage
              (encodeBoolWordAppend result []) =
            List.append (encodeNatAppend stage [])
              (encodeBoolWordAppend result []) := by
        simpa using
          encodeNatAppend_append stage ([] : Word MachineCodeSymbol)
            (encodeBoolWordAppend result [])
      have hbool :
          encodeBoolWordAppend input
              (List.append (encodeNatAppend stage [])
                (encodeBoolWordAppend result [])) =
            List.append
              (encodeBoolWordAppend input
                (encodeNatAppend stage []))
              (encodeBoolWordAppend result []) :=
        encodeBoolWordAppend_append input
          (encodeNatAppend stage [])
          (encodeBoolWordAppend result [])
      simp [PairedRecognizerDovetailControllerStageInputCode,
        DovetailControllerLayout.encode,
        DovetailControllerLayout.encodeAppend,
        DovetailControllerLayout.stageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend]
      change
        MachineCodeSymbol.header ::
            encodeBoolWordAppend input
              (encodeNatAppend stage
                (encodeBoolWordAppend result [])) =
          MachineCodeSymbol.header ::
            List.append
              (encodeBoolWordAppend input
                (encodeNatAppend stage []))
              (encodeBoolWordAppend result [])
      rw [hnat, hbool]

theorem encodeTapeAppend_append
    (T : Tape Bool) (suffix tail : Word MachineCodeSymbol) :
    encodeTapeAppend T (List.append suffix tail) =
      List.append (encodeTapeAppend T suffix) tail := by
  cases T with
  | mk left head right =>
      simp [encodeTapeAppend]
      change
        encodeCellListAppend left
            (encodeCellAppend head
              (encodeCellListAppend right
                (List.append suffix tail))) =
          List.append
            (encodeCellListAppend left
              (encodeCellAppend head
                (encodeCellListAppend right suffix)))
            tail
      rw [encodeCellListAppend_append right suffix tail]
      rw [encodeCellAppend_append head
        (encodeCellListAppend right suffix) tail]
      rw [encodeCellListAppend_append left
        (encodeCellAppend head
          (encodeCellListAppend right suffix)) tail]

theorem encodeConfigurationAppend_append
    (c : Configuration)
    (suffix tail : Word MachineCodeSymbol) :
    encodeConfigurationAppend c
        (List.append suffix tail) =
      List.append
        (encodeConfigurationAppend c suffix) tail := by
  cases c with
  | mk state tape =>
      simp [encodeConfigurationAppend]
      change
        encodeNatAppend state
            (encodeTapeAppend tape
              (List.append suffix tail)) =
          List.append
            (encodeNatAppend state
              (encodeTapeAppend tape suffix))
            tail
      rw [encodeTapeAppend_append tape suffix tail]
      rw [encodeNatAppend_append state
        (encodeTapeAppend tape suffix) tail]

theorem encodeCodeWordAsInput_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeBoolWordAppend w suffix) =
      List.append
        (encodeCodeWordAsInput
          (encodeBoolWord w))
        (encodeCodeWordAsInput suffix) := by
  have h :=
    encodeBoolWordAppend_append w ([] : Word MachineCodeSymbol) suffix
  simp at h
  rw [h]
  change
    encodeCodeWordAsInput
        (List.append (encodeBoolWordAppend w []) suffix) =
      List.append
        (encodeCodeWordAsInput
          (encodeBoolWord w))
        (encodeCodeWordAsInput suffix)
  rw [encodeCodeWordAsInput_append]
  rfl

/-!
## Encoding length bounds

These opt-in length facts support tape-window monotonicity checks for concrete
rewriters.  They are kept out of the global simp set so downstream scanner
proofs can choose when to expose encoding lengths.
-/

theorem encodeCellsAppend_length
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    (encodeCellsAppend cells suffix).length =
      cells.length + suffix.length := by
  induction cells with
  | nil =>
      simp [encodeCellsAppend]
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [encodeCellsAppend,
            encodeCellAppend,
            encodeCell, ih]
          omega
      | some b =>
          cases b <;>
            simp [encodeCellsAppend,
              encodeCellAppend,
              encodeCell, ih] <;>
            omega

theorem encodeCellListAppend_length_ge
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    cells.length + suffix.length <=
      (encodeCellListAppend cells suffix).length := by
  simp [encodeCellListAppend,
    encodeNatAppend, encodeCellsAppend_length,
    List.length_append]

theorem encodeBoolWordAppend_length_ge
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    w.length + suffix.length <=
      (encodeBoolWordAppend w suffix).length := by
  simpa [encodeBoolWordAppend] using
    encodeCellListAppend_length_ge (w.map some) suffix

theorem encodeCodeSymbolAsInput_length
    (symbol : MachineCodeSymbol) :
    (encodeCodeSymbolAsInput symbol).length = 4 := by
  cases symbol <;> rfl

theorem encodeCodeWordAsInput_length
    (tokens : Word MachineCodeSymbol) :
    (encodeCodeWordAsInput tokens).length =
      4 * tokens.length := by
  induction tokens with
  | nil =>
      rfl
  | cons symbol rest ih =>
      simp [encodeCodeWordAsInput,
        encodeCodeSymbolAsInput_length, ih, Nat.mul_add, Nat.add_comm]

/-!
## Decoder-backed cancellation

The structured encoders below are self-delimiting: decoding an encoded prefix
returns both the payload and the unconsumed suffix.  These lemmas package the
standard proof pattern "decode both sides, then compare the returned pairs".
They are intentionally not provided for raw {name}`encodeCellsAppend`,
whose split between payload cells and suffix is not unique without the
length-prefixed wrapper.
-/

theorem encodeNatAppend_inj
    {n m : Nat}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeNatAppend n suffix =
        encodeNatAppend m tail) :
    n = m ∧ suffix = tail := by
  have hdecode :
      decodeNat
          (encodeNatAppend n suffix) =
        decodeNat
          (encodeNatAppend m tail) := by
    rw [h]
  have hpair : (n, suffix) = (m, tail) := by
    simpa [decodeNat_encodeNatAppend] using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeCellAppend_inj
    {cell other : Option Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeCellAppend cell suffix =
        encodeCellAppend other tail) :
    cell = other ∧ suffix = tail := by
  have hdecode :
      decodeCell
          (encodeCellAppend cell suffix) =
        decodeCell
          (encodeCellAppend other tail) := by
    rw [h]
  have hpair : (cell, suffix) = (other, tail) := by
    simpa [decodeCell_encodeCellAppend] using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeBoolAppend_inj
    {b c : Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeBoolAppend b suffix =
        encodeBoolAppend c tail) :
    b = c ∧ suffix = tail := by
  simpa [encodeBoolAppend] using
    encodeCellAppend_inj h

theorem encodeDirectionAppend_inj
    {dir other : Direction}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeDirectionAppend dir suffix =
        encodeDirectionAppend other tail) :
    dir = other ∧ suffix = tail := by
  have hdecode :
      decodeDirection
          (encodeDirectionAppend dir suffix) =
        decodeDirection
          (encodeDirectionAppend other tail) := by
    rw [h]
  have hpair : (dir, suffix) = (other, tail) := by
    simpa [decodeDirection_encodeDirectionAppend] using
      hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeCellListAppend_inj
    {cells other : List (Option Bool)}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeCellListAppend cells suffix =
        encodeCellListAppend other tail) :
    cells = other ∧ suffix = tail := by
  have hdecode :
      decodeCellList
          (encodeCellListAppend cells suffix) =
        decodeCellList
          (encodeCellListAppend other tail) := by
    rw [h]
  have hpair : (cells, suffix) = (other, tail) := by
    simpa [decodeCellList_encodeCellListAppend] using
      hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeBoolWordAppend_inj
    {w v : Word Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeBoolWordAppend w suffix =
        encodeBoolWordAppend v tail) :
    w = v ∧ suffix = tail := by
  have hdecode :
      decodeBoolWord
          (encodeBoolWordAppend w suffix) =
        decodeBoolWord
          (encodeBoolWordAppend v tail) := by
    rw [h]
  have hpair : (w, suffix) = (v, tail) := by
    simpa [decodeBoolWord_encodeBoolWordAppend] using
      hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeTapeAppend_inj
    {T U : Tape Bool}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeTapeAppend T suffix =
        encodeTapeAppend U tail) :
    T = U ∧ suffix = tail := by
  have hdecode :
      decodeTape
          (encodeTapeAppend T suffix) =
        decodeTape
          (encodeTapeAppend U tail) := by
    rw [h]
  have hpair : (T, suffix) = (U, tail) := by
    simpa [decodeTape_encodeTapeAppend] using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeConfigurationAppend_inj
    {c d : Configuration}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeConfigurationAppend c suffix =
        encodeConfigurationAppend d tail) :
    c = d ∧ suffix = tail := by
  have hdecode :
      decodeConfiguration
          (encodeConfigurationAppend c suffix) =
        decodeConfiguration
          (encodeConfigurationAppend d tail) := by
    rw [h]
  have hpair : (c, suffix) = (d, tail) := by
    simpa [decodeConfiguration_encodeConfigurationAppend]
      using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeTransitionAppend_inj
    {t u : TransitionDescription}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeTransitionAppend t suffix =
        encodeTransitionAppend u tail) :
    t = u ∧ suffix = tail := by
  have hdecode :
      decodeTransition
          (encodeTransitionAppend t suffix) =
        decodeTransition
          (encodeTransitionAppend u tail) := by
    rw [h]
  have hpair : (t, suffix) = (u, tail) := by
    simpa [decodeTransition_encodeTransition_append]
      using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem encodeDescriptionAppend_inj
    {D E : MachineDescription}
    {suffix tail : Word MachineCodeSymbol}
    (h :
      encodeDescriptionAppend D suffix =
        encodeDescriptionAppend E tail) :
    D = E ∧ suffix = tail := by
  have hdecode :
      decodeDescriptionPrefix
          (encodeDescriptionAppend D suffix) =
        decodeDescriptionPrefix
          (encodeDescriptionAppend E tail) := by
    rw [h]
  have hpair : (D, suffix) = (E, tail) := by
    simpa [decodeDescriptionPrefix_encodeDescriptionAppend]
      using hdecode
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end Computability
end FoC

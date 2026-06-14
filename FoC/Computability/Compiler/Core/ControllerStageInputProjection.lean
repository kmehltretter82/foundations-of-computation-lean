import FoC.Computability.Compiler.Core.EncodedRewriters

set_option doc.verso true

/-!
# Controller stage-input projection machine
-/

namespace FoC
namespace Computability

open Languages

def dovetailControllerProjectionKeep
    (source : Nat) (cell : Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source (some cell) (some cell)
    Direction.right target

def dovetailControllerProjectionErase
    (source : Nat) (cell : Option Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source cell none Direction.right target

def dovetailControllerProjectionKeepMove
    (source : Nat) (cell : Option Bool) (move : Direction) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source cell cell move target

def dovetailControllerProjectionWriteMove
    (source : Nat) (read write : Option Bool) (move : Direction)
    (target : Nat) : TransitionDescription :=
  MachineDescription.transition source read write move target

def dovetailControllerProjectionScanLeftToBoundary
    (scan one two three found : Nat) : List TransitionDescription :=
  [ dovetailControllerProjectionKeepMove scan none Direction.left one
  , dovetailControllerProjectionKeepMove scan (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove scan (some true) Direction.left scan
  , dovetailControllerProjectionKeepMove one none Direction.left two
  , dovetailControllerProjectionKeepMove one (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove one (some true) Direction.left scan
  , dovetailControllerProjectionKeepMove two none Direction.left three
  , dovetailControllerProjectionKeepMove two (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove two (some true) Direction.left scan
  , dovetailControllerProjectionKeepMove three none Direction.right found
  , dovetailControllerProjectionKeepMove three (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove three (some true) Direction.left scan ]

private def transitionWellFormedBool
    (stateCount : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source < stateCount) && decide (t.target < stateCount)

private def transitionSameKeyBool
    (t u : TransitionDescription) : Bool :=
  decide (t.source = u.source) && decide (t.read = u.read)

private def transitionSameActionBool
    (t u : TransitionDescription) : Bool :=
  decide (t.write = u.write) && decide (t.move = u.move) &&
    decide (t.target = u.target)

private def transitionDeterministicPairBool
    (t u : TransitionDescription) : Bool :=
  !transitionSameKeyBool t u || transitionSameActionBool t u

private def transitionNotFromBool
    (state : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source ≠ state)

private theorem transition_wellFormed_of_all
    {stateCount : Nat} {l : List TransitionDescription}
    (h : l.all (transitionWellFormedBool stateCount) = true) :
    forall t : TransitionDescription,
      t ∈ l -> TransitionDescription.WellFormed stateCount t := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [transitionWellFormedBool, TransitionDescription.WellFormed] using
    htbool

private theorem transition_deterministic_of_all
    {l : List TransitionDescription}
    (h :
      l.all (fun t =>
        l.all (fun u => transitionDeterministicPairBool t u)) = true) :
    forall t u : TransitionDescription,
      t ∈ l ->
      u ∈ l ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  have htbool := (List.all_eq_true.mp h) t ht
  have hubool := (List.all_eq_true.mp htbool) u hu
  have hkeyBool :
      transitionSameKeyBool t u = true := by
    simpa [transitionSameKeyBool, TransitionDescription.SameKey] using hkey
  simp [transitionDeterministicPairBool, hkeyBool, transitionSameActionBool,
    TransitionDescription.SameAction] at hubool ⊢
  rcases hubool with ⟨⟨hwrite, hmove⟩, htarget⟩
  exact ⟨hwrite, hmove, htarget⟩

private theorem transition_notFrom_of_all
    {state : Nat} {l : List TransitionDescription}
    (h : l.all (transitionNotFromBool state) = true) :
    forall t : TransitionDescription, t ∈ l -> t.source ≠ state := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  exact of_decide_eq_true htbool

private def projectionTapeAtCells
    (leftRev : List (Option Bool)) : List (Option Bool) -> Tape Bool
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

private def projectionTapeAt
    (leftRev : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  projectionTapeAtCells leftRev (bits.map some)

private def projectionConfig
    (state : Nat) (leftRev cells : List (Option Bool)) :
    MachineDescription.Configuration :=
  { state := state, tape := projectionTapeAtCells leftRev cells }

private def projectionCodeCells
    (code : Word MachineCodeSymbol) : List (Option Bool) :=
  (MachineDescription.encodeCodeWordAsInput code).map some

private def projectionTickCodeCells : List (Option Bool) :=
  (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.tick).map some

private def projectionTickCodeCellsRev : List (Option Bool) :=
  projectionTickCodeCells.reverse

private def projectionDoneCodeCells : List (Option Bool) :=
  (MachineDescription.encodeCodeSymbolAsInput MachineCodeSymbol.done).map some

private def projectionMarkedTickCodeCells : List (Option Bool) :=
  [some false, some false, some true, none]

private def projectionBoolCellCodeCells (b : Bool) : List (Option Bool) :=
  (MachineDescription.encodeCodeSymbolAsInput
    (if b then MachineCodeSymbol.one else MachineCodeSymbol.zero)).map some

private def projectionMarkedBoolCellCodeCells : Bool -> List (Option Bool)
  | false => [some false, none, some false, some true]
  | true => [some false, none, some true, some false]

private def projectionRepeatedCells
    (chunk : List (Option Bool)) : Nat -> List (Option Bool)
  | 0 => []
  | n + 1 => List.append chunk (projectionRepeatedCells chunk n)

private theorem projectionRepeatedCells_succ_right
    (chunk : List (Option Bool)) (n : Nat) :
    projectionRepeatedCells chunk (n + 1) =
      List.append (projectionRepeatedCells chunk n) chunk := by
  induction n with
  | zero =>
      simp [projectionRepeatedCells]
  | succ n ih =>
      change
        List.append chunk (projectionRepeatedCells chunk (n + 1)) =
          List.append (List.append chunk (projectionRepeatedCells chunk n))
            chunk
      rw [ih]
      simp [List.append_assoc]

private def projectionBoolPayloadCells : Word Bool -> List (Option Bool)
  | [] => []
  | b :: rest =>
      List.append (projectionBoolCellCodeCells b)
        (projectionBoolPayloadCells rest)

private def projectionMarkedBoolPayloadCells : Word Bool -> List (Option Bool)
  | [] => []
  | b :: rest =>
      List.append (projectionMarkedBoolCellCodeCells b)
        (projectionMarkedBoolPayloadCells rest)

private def projectionBoolWordWorkCells
    (marked rest : Word Bool) (suffix : Word MachineCodeSymbol) :
    List (Option Bool) :=
  List.append
    (projectionRepeatedCells projectionMarkedTickCodeCells marked.length)
    (List.append
      (projectionCodeCells (List.replicate rest.length MachineCodeSymbol.tick))
      (List.append projectionDoneCodeCells
        (List.append (projectionMarkedBoolPayloadCells marked)
          (List.append (projectionBoolPayloadCells rest)
            (projectionCodeCells suffix)))))

private def projectionAllMarkedBoolWordCells (w : Word Bool) :
    List (Option Bool) :=
  List.append
    (projectionRepeatedCells projectionMarkedTickCodeCells w.length)
    (List.append projectionDoneCodeCells
      (projectionMarkedBoolPayloadCells w))

private def projectionStageTickCellsRev (stage : Nat) : List (Option Bool) :=
  (projectionCodeCells (List.replicate stage MachineCodeSymbol.tick)).reverse

private theorem projectionCodeCells_append
    (pre suffix : Word MachineCodeSymbol) :
    projectionCodeCells (List.append pre suffix) =
      List.append (projectionCodeCells pre) (projectionCodeCells suffix) := by
  unfold projectionCodeCells
  rw [MachineDescription.encodeCodeWordAsInput_append]
  simp [List.map_append]

private theorem projectionCodeCells_filterMap
    (code : Word MachineCodeSymbol) :
    (projectionCodeCells code).filterMap (fun cell => cell) =
      MachineDescription.encodeCodeWordAsInput code := by
  simpa [projectionCodeCells] using
    Tape.filterMap_id_map_some
      (MachineDescription.encodeCodeWordAsInput code)

private theorem encodeNatAppend_append
    (n : Nat) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend n (List.append suffix tail) =
      List.append (MachineDescription.encodeNatAppend n suffix) tail := by
  simp [MachineDescription.encodeNatAppend, List.append_assoc]

private theorem encodeCellsAppend_append
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

private theorem encodeCellListAppend_append
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

private theorem encodeBoolWordAppend_append
    (w : Word Bool) (suffix tail : Word MachineCodeSymbol) :
    MachineDescription.encodeBoolWordAppend w (List.append suffix tail) =
      List.append (MachineDescription.encodeBoolWordAppend w suffix)
        tail := by
  simpa [MachineDescription.encodeBoolWordAppend] using
    encodeCellListAppend_append (w.map some) suffix tail

private theorem encodeNat_eq_replicate_tick_done
    (n : Nat) :
    MachineDescription.encodeNat n =
      List.append (List.replicate n MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [MachineDescription.encodeNat, ih, List.replicate_succ]

private theorem encodeCodeWordAsInput_encodeBoolWordAppend
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

private theorem encodeCodeWordAsInput_encodeNat
    (n : Nat) :
    MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeNat n) =
      List.append
        (MachineDescription.encodeCodeWordAsInput
          (List.replicate n MachineCodeSymbol.tick))
        (MachineDescription.encodeCodeWordAsInput [MachineCodeSymbol.done]) := by
  rw [encodeNat_eq_replicate_tick_done,
    MachineDescription.encodeCodeWordAsInput_append]

private theorem projectionDoneCodeCells_filterMap :
    projectionDoneCodeCells.filterMap (fun cell => cell) =
      MachineDescription.encodeCodeWordAsInput [MachineCodeSymbol.done] := by
  simpa [projectionDoneCodeCells] using
    projectionCodeCells_filterMap [MachineCodeSymbol.done]

private theorem projectionCodeCells_replicate_tick
    (n : Nat) :
    projectionCodeCells (List.replicate n MachineCodeSymbol.tick) =
      projectionRepeatedCells projectionTickCodeCells n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have htail :
          List.map some
              (MachineDescription.encodeCodeWordAsInput
                (List.replicate n MachineCodeSymbol.tick)) =
            projectionRepeatedCells
              (List.map some
                (MachineDescription.encodeCodeSymbolAsInput
                  MachineCodeSymbol.tick)) n := by
        simpa [projectionCodeCells, projectionTickCodeCells] using ih
      have hrep :
          List.replicate (n + 1) MachineCodeSymbol.tick =
            MachineCodeSymbol.tick ::
              List.replicate n MachineCodeSymbol.tick := by
        rw [show n + 1 = Nat.succ n by omega]
        rfl
      rw [hrep]
      simp [projectionCodeCells, projectionRepeatedCells,
        projectionTickCodeCells, MachineDescription.encodeCodeWordAsInput,
        htail]

private theorem projectionBoolPayloadCells_eq
    (w : Word Bool) :
    projectionBoolPayloadCells w =
      projectionCodeCells ((w.map fun b =>
        if b then MachineCodeSymbol.one else MachineCodeSymbol.zero)) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [projectionBoolPayloadCells, projectionBoolCellCodeCells,
          projectionCodeCells, MachineDescription.encodeCodeWordAsInput, ih]

private theorem projectionCodeCells_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    projectionCodeCells (MachineDescription.encodeNatAppend n suffix) =
      List.append (projectionCodeCells
        (List.replicate n MachineCodeSymbol.tick))
        (List.append projectionDoneCodeCells (projectionCodeCells suffix)) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hrep :
          projectionCodeCells (List.replicate (n + 1) MachineCodeSymbol.tick) =
            List.append projectionTickCodeCells
              (projectionCodeCells (List.replicate n MachineCodeSymbol.tick)) := by
        have hrep' :
            List.replicate (n + 1) MachineCodeSymbol.tick =
              MachineCodeSymbol.tick ::
                List.replicate n MachineCodeSymbol.tick := by
          rw [show n + 1 = Nat.succ n by omega]
          rfl
        rw [hrep']
        rfl
      rw [hrep]
      change
        List.append projectionTickCodeCells
            (projectionCodeCells
              (MachineDescription.encodeNatAppend n suffix)) =
          List.append
            (List.append projectionTickCodeCells
              (projectionCodeCells
                (List.replicate n MachineCodeSymbol.tick)))
            (List.append projectionDoneCodeCells
              (projectionCodeCells suffix))
      rw [ih]
      simp [List.append_assoc]

private theorem projectionBoolPayloadCells_append_eq_encodeCellsAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    List.append (projectionBoolPayloadCells w) (projectionCodeCells suffix) =
      projectionCodeCells
        (MachineDescription.encodeCellsAppend (w.map some) suffix) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b
      · simp [projectionBoolPayloadCells, projectionBoolCellCodeCells,
          projectionCodeCells, MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend, MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput, List.append_assoc]
        simpa [projectionCodeCells] using ih
      · simp [projectionBoolPayloadCells, projectionBoolCellCodeCells,
          projectionCodeCells, MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend, MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput, List.append_assoc]
        simpa [projectionCodeCells] using ih

private theorem projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    projectionBoolWordWorkCells [] w suffix =
      projectionCodeCells (MachineDescription.encodeBoolWordAppend w suffix) := by
  simp [projectionBoolWordWorkCells, projectionRepeatedCells,
    projectionMarkedBoolPayloadCells, MachineDescription.encodeBoolWordAppend,
    MachineDescription.encodeCellListAppend,
    projectionCodeCells_encodeNatAppend]
  exact projectionBoolPayloadCells_append_eq_encodeCellsAppend w suffix

def DovetailControllerStageInputProjectionDescription :
    MachineDescription where
  stateCount := 1000
  start := 0
  halt := 999
  transitions :=
    [ dovetailControllerProjectionErase 0 (some false) 1
    , dovetailControllerProjectionErase 1 (some false) 2
    , dovetailControllerProjectionErase 2 (some false) 3
    , dovetailControllerProjectionErase 3 (some false) 100

    -- Validate the input bool-word length prefix, marking ticks and cells.
    , dovetailControllerProjectionKeep 100 false 101
    , dovetailControllerProjectionKeep 101 false 102
    , dovetailControllerProjectionKeep 102 true 103
    , dovetailControllerProjectionWriteMove 103 (some false) none Direction.right 120
    , dovetailControllerProjectionKeep 103 true 150
    , dovetailControllerProjectionKeepMove 103 none Direction.right 100

    -- Skip the remaining input length prefix to find the matching cell.
    , dovetailControllerProjectionKeep 120 false 121
    , dovetailControllerProjectionKeep 121 false 122
    , dovetailControllerProjectionKeep 122 true 123
    , dovetailControllerProjectionKeep 123 false 120
    , dovetailControllerProjectionKeep 123 true 130
    , dovetailControllerProjectionKeepMove 123 none Direction.right 120

    -- Mark one unprocessed input cell for the tick just marked.
    , dovetailControllerProjectionKeep 130 false 131
    , dovetailControllerProjectionWriteMove 131 (some true) none Direction.right 132
    , dovetailControllerProjectionKeepMove 131 none Direction.right 135
    , dovetailControllerProjectionKeep 132 false 133
    , dovetailControllerProjectionKeep 132 true 134
    , dovetailControllerProjectionKeepMove 133 (some true) Direction.left 140
    , dovetailControllerProjectionKeepMove 134 (some false) Direction.left 140
    , dovetailControllerProjectionKeep 135 false 136
    , dovetailControllerProjectionKeep 135 true 137
    , dovetailControllerProjectionKeep 136 true 130
    , dovetailControllerProjectionKeep 137 false 130

    -- No unmarked ticks remain: ensure all input cells were processed.
    , dovetailControllerProjectionKeep 150 false 151
    , dovetailControllerProjectionKeepMove 151 none Direction.right 152
    , dovetailControllerProjectionKeepMove 151 (some false) Direction.left 160
    , dovetailControllerProjectionKeep 152 false 153
    , dovetailControllerProjectionKeep 152 true 154
    , dovetailControllerProjectionKeep 153 true 150
    , dovetailControllerProjectionKeep 154 false 150

    -- Restore the marked input prefix, then continue at the stage nat.
    , dovetailControllerProjectionKeepMove 164 none Direction.right 165
    , dovetailControllerProjectionKeepMove 165 none Direction.right 166
    , dovetailControllerProjectionKeepMove 166 none Direction.right 170
    , dovetailControllerProjectionKeep 170 false 171
    , dovetailControllerProjectionKeep 171 false 172
    , dovetailControllerProjectionKeep 172 true 173
    , dovetailControllerProjectionKeep 173 false 170
    , dovetailControllerProjectionWriteMove 173 none (some false) Direction.right 170
    , dovetailControllerProjectionKeep 173 true 180
    , dovetailControllerProjectionKeep 180 false 181
    , dovetailControllerProjectionWriteMove 181 none (some true) Direction.right 182
    , dovetailControllerProjectionKeepMove 181 (some false) Direction.left 200
    , dovetailControllerProjectionKeep 182 false 183
    , dovetailControllerProjectionKeep 182 true 184
    , dovetailControllerProjectionKeep 183 true 180
    , dovetailControllerProjectionKeep 184 false 180

    -- Preserve and validate the stage nat prefix.
    , dovetailControllerProjectionKeep 200 false 201
    , dovetailControllerProjectionKeep 201 false 202
    , dovetailControllerProjectionKeep 202 true 203
    , dovetailControllerProjectionKeep 203 false 200
    , dovetailControllerProjectionKeep 203 true 210

    -- Mark the stage-nat terminator as a four-blank boundary.
    , dovetailControllerProjectionKeepMove 210 (some false) Direction.left 211
    , dovetailControllerProjectionWriteMove 211 (some true) none Direction.left 212
    , dovetailControllerProjectionWriteMove 212 (some true) none Direction.left 213
    , dovetailControllerProjectionWriteMove 213 (some false) none Direction.left 214
    , dovetailControllerProjectionWriteMove 214 (some false) none Direction.right 215
    , dovetailControllerProjectionKeepMove 215 none Direction.right 216
    , dovetailControllerProjectionKeepMove 216 none Direction.right 217
    , dovetailControllerProjectionKeepMove 217 none Direction.right 300

    -- Validate the result bool-word length prefix, marking ticks and cells.
    , dovetailControllerProjectionKeep 300 false 301
    , dovetailControllerProjectionKeep 301 false 302
    , dovetailControllerProjectionKeep 302 true 303
    , dovetailControllerProjectionWriteMove 303 (some false) none Direction.right 320
    , dovetailControllerProjectionKeep 303 true 350
    , dovetailControllerProjectionKeepMove 303 none Direction.right 300

    -- Skip the remaining result length prefix to find the matching cell.
    , dovetailControllerProjectionKeep 320 false 321
    , dovetailControllerProjectionKeep 321 false 322
    , dovetailControllerProjectionKeep 322 true 323
    , dovetailControllerProjectionKeep 323 false 320
    , dovetailControllerProjectionKeep 323 true 330
    , dovetailControllerProjectionKeepMove 323 none Direction.right 320

    -- Mark one unprocessed result cell for the tick just marked.
    , dovetailControllerProjectionKeep 330 false 331
    , dovetailControllerProjectionWriteMove 331 (some true) none Direction.right 332
    , dovetailControllerProjectionKeepMove 331 none Direction.right 335
    , dovetailControllerProjectionKeep 332 false 333
    , dovetailControllerProjectionKeep 332 true 334
    , dovetailControllerProjectionKeepMove 333 (some true) Direction.left 340
    , dovetailControllerProjectionKeepMove 334 (some false) Direction.left 340
    , dovetailControllerProjectionKeep 335 false 336
    , dovetailControllerProjectionKeep 335 true 337
    , dovetailControllerProjectionKeep 336 true 330
    , dovetailControllerProjectionKeep 337 false 330

    -- No unmarked ticks remain: ensure all result cells were processed.
    , dovetailControllerProjectionKeep 350 false 351
    , dovetailControllerProjectionKeepMove 350 none Direction.left 360
    , dovetailControllerProjectionKeepMove 351 none Direction.right 352
    , dovetailControllerProjectionKeep 352 false 353
    , dovetailControllerProjectionKeep 352 true 354
    , dovetailControllerProjectionKeep 353 true 350
    , dovetailControllerProjectionKeep 354 false 350

    -- Restore the stage-nat terminator boundary.
    , dovetailControllerProjectionWriteMove 363 none (some false) Direction.right 364
    , dovetailControllerProjectionWriteMove 364 none (some false) Direction.right 365
    , dovetailControllerProjectionWriteMove 365 none (some true) Direction.right 366
    , dovetailControllerProjectionWriteMove 366 none (some true) Direction.right 367

    -- Blank the validated result length prefix and cell payload.
    , dovetailControllerProjectionErase 367 (some false) 368
    , dovetailControllerProjectionErase 368 (some false) 369
    , dovetailControllerProjectionErase 369 (some true) 370
    , dovetailControllerProjectionErase 370 (some false) 367
    , dovetailControllerProjectionErase 370 none 367
    , dovetailControllerProjectionErase 370 (some true) 380
    , dovetailControllerProjectionErase 380 (some false) 381
    , dovetailControllerProjectionErase 380 none 999
    , dovetailControllerProjectionErase 381 none 382
    , dovetailControllerProjectionErase 382 (some false) 383
    , dovetailControllerProjectionErase 382 (some true) 384
    , dovetailControllerProjectionErase 383 (some true) 380
    , dovetailControllerProjectionErase 384 (some false) 380 ]
      ++ dovetailControllerProjectionScanLeftToBoundary 140 141 142 143 144
      ++
    [ dovetailControllerProjectionKeepMove 144 none Direction.right 145
    , dovetailControllerProjectionKeepMove 145 none Direction.right 146
    , dovetailControllerProjectionKeepMove 146 none Direction.right 100 ]
      ++ dovetailControllerProjectionScanLeftToBoundary 160 161 162 163 164
      ++ dovetailControllerProjectionScanLeftToBoundary 340 341 342 343 344
      ++
    [ dovetailControllerProjectionKeepMove 344 none Direction.right 345
    , dovetailControllerProjectionKeepMove 345 none Direction.right 346
    , dovetailControllerProjectionKeepMove 346 none Direction.right 300 ]
      ++
    [ dovetailControllerProjectionKeepMove 360 none Direction.left 361
    , dovetailControllerProjectionKeepMove 360 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 360 (some true) Direction.left 360
    , dovetailControllerProjectionKeepMove 361 none Direction.left 362
    , dovetailControllerProjectionKeepMove 361 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 361 (some true) Direction.left 360
    , dovetailControllerProjectionKeepMove 362 none Direction.left 363
    , dovetailControllerProjectionKeepMove 362 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 362 (some true) Direction.left 360
    , dovetailControllerProjectionKeepMove 363 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 363 (some true) Direction.left 360 ]

theorem dovetailControllerStageInputProjectionDescription_wellFormed :
    DovetailControllerStageInputProjectionDescription.WellFormed := by
  constructor
  · simp [DovetailControllerStageInputProjectionDescription]
  constructor
  · simp [DovetailControllerStageInputProjectionDescription]
  constructor
  · simp [DovetailControllerStageInputProjectionDescription]
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := DovetailControllerStageInputProjectionDescription.transitions)
      (stateCount := DovetailControllerStageInputProjectionDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := DovetailControllerStageInputProjectionDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem dovetailControllerStageInputProjectionDescription_haltTransitionFree :
    DovetailControllerStageInputProjectionDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := DovetailControllerStageInputProjectionDescription.transitions)
    (state := DovetailControllerStageInputProjectionDescription.halt)
    (by
      native_decide) t ht

private theorem dovetailControllerStageInputProjectionDescription_run_header
    (suffix : Word Bool) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (DovetailControllerStageInputProjectionDescription.initial
          (List.append [false, false, false, false] suffix)) =
      { state := 100
        tape := projectionTapeAt [none, none, none, none] suffix } := by
  cases suffix with
  | nil =>
      rfl
  | cons b _ =>
      cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_stage_tick
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 200 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 200
        (List.append projectionTickCodeCellsRev leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell _ =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_stage_done
    (leftRev rest : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 12
        (projectionConfig 200 leftRev
          (List.append projectionDoneCodeCells (some false :: rest))) =
      projectionConfig 300
        (List.append [none, none, none, none] leftRev)
        (some false :: rest) := by
  rfl

private theorem projectionStageTickCellsRev_succ
    (stage : Nat) :
    projectionStageTickCellsRev (stage + 1) =
      List.append (projectionStageTickCellsRev stage)
        projectionTickCodeCellsRev := by
  have hsucc : stage + 1 = Nat.succ stage := by omega
  rw [hsucc]
  simp [List.replicate_succ, projectionStageTickCellsRev,
    projectionCodeCells, projectionTickCodeCells,
    projectionTickCodeCellsRev, MachineDescription.encodeCodeWordAsInput,
    List.reverse_append]

private theorem dovetailControllerStageInputProjectionDescription_run_stage_nat
    (stage : Nat) (leftRev : List (Option Bool)) (result : Word Bool) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (4 * stage + 12)
        (projectionConfig 200 leftRev
          (projectionCodeCells
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeBoolWord result)))) =
      projectionConfig 300
        (List.append [none, none, none, none]
          (List.append (projectionStageTickCellsRev stage) leftRev))
        (projectionCodeCells (MachineDescription.encodeBoolWord result)) := by
  induction stage generalizing leftRev with
  | zero =>
      cases result with
      | nil =>
          rfl
      | cons b _ =>
          cases b <;> rfl
  | succ stage ih =>
      have hsteps : 4 * (stage + 1) + 12 = 4 + (4 * stage + 12) := by
        omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * stage + 12)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 200 leftRev
              (projectionCodeCells
                (MachineDescription.encodeNatAppend (stage + 1)
                  (MachineDescription.encodeBoolWord result))))) = _
      have hsucc : stage + 1 = Nat.succ stage := by omega
      have hcells :
          projectionCodeCells
              (MachineDescription.encodeNatAppend (stage + 1)
                (MachineDescription.encodeBoolWord result)) =
            List.append projectionTickCodeCells
              (projectionCodeCells
                (MachineDescription.encodeNatAppend stage
                  (MachineDescription.encodeBoolWord result))) := by
        rw [hsucc]
        rfl
      rw [hcells]
      rw [dovetailControllerStageInputProjectionDescription_run_stage_tick]
      rw [ih]
      rw [projectionStageTickCellsRev_succ]
      simp [projectionConfig, projectionTapeAtCells, List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_marked_tick
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 367 leftRev
          (List.append projectionMarkedTickCodeCells tail)) =
      projectionConfig 367
        (List.append [none, none, none, none] leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_marked_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig (4 * count)
        (projectionConfig 367 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells count)
            tail)) =
      projectionConfig 367
        (List.append (List.replicate (4 * count) none) leftRev) tail := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      have hsteps : 4 * (count + 1) = 4 + 4 * count := by omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * count)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 367 leftRev
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  (count + 1)) tail))) = _
      rw [show projectionRepeatedCells projectionMarkedTickCodeCells
          (count + 1) =
          List.append projectionMarkedTickCodeCells
            (projectionRepeatedCells projectionMarkedTickCodeCells count) by
        rfl]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * count)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 367 leftRev
              (List.append projectionMarkedTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells count)
                  tail)))) = _
      rw [dovetailControllerStageInputProjectionDescription_run_cleanup_marked_tick]
      rw [ih]
      rw [show 4 + 4 * count = 4 * count + 4 by omega]
      have hrep :
          List.replicate (4 * count + 4) (none : Option Bool) =
            List.append (List.replicate (4 * count) (none : Option Bool))
              ([none, none, none, none] : List (Option Bool)) := by
        simp [List.replicate_succ', List.append_assoc]
      rw [hrep]
      simp [List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_done
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 367 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 380
        (List.append [none, none, none, none] leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 380 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 380
        (List.append [none, none, none, none] leftRev) tail := by
  cases b <;>
    cases tail with
    | nil =>
        rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload
    (w : Word Bool) (leftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (4 * w.length + 1)
        (projectionConfig 380 leftRev
          (projectionMarkedBoolPayloadCells w)) =
      projectionConfig 999
        (List.append (List.replicate (4 * w.length + 1) none)
          leftRev) [] := by
  induction w generalizing leftRev with
  | nil =>
      rfl
  | cons b rest ih =>
      have hsteps :
          4 * (b :: rest).length + 1 = 4 + (4 * rest.length + 1) := by
        simp
        omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * rest.length + 1)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 380 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest)))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload_cell]
      rw [ih]
      rw [show 4 + (4 * rest.length + 1) =
          (4 * rest.length + 1) + 4 by omega]
      have hrep :
          List.replicate (4 * rest.length + 1 + 4)
              (none : Option Bool) =
            List.append
              (List.replicate (4 * rest.length + 1)
                (none : Option Bool))
              ([none, none, none, none] : List (Option Bool)) := by
        simp [List.replicate_succ', List.append_assoc]
      rw [hrep]
      simp [List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload_to_tail
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (4 * w.length)
        (projectionConfig 380 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 380
        (List.append (List.replicate (4 * w.length) none)
          leftRev) tail := by
  induction w generalizing leftRev with
  | nil =>
      rfl
  | cons b rest ih =>
      have hsteps :
          4 * (b :: rest).length = 4 + 4 * rest.length := by
        simp
        omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * rest.length)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 380 leftRev
              (List.append (projectionMarkedBoolPayloadCells (b :: rest))
                tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      have hcells :
          List.append
              (List.append (projectionMarkedBoolCellCodeCells b)
                (projectionMarkedBoolPayloadCells rest)) tail =
            List.append (projectionMarkedBoolCellCodeCells b)
              (List.append (projectionMarkedBoolPayloadCells rest) tail) := by
        simp [List.append_assoc]
      rw [hcells]
      rw [dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload_cell
        (tail := List.append (projectionMarkedBoolPayloadCells rest) tail)]
      rw [ih]
      rw [show 4 + 4 * rest.length =
          4 * rest.length + 4 by omega]
      have hrep :
          List.replicate (4 * rest.length + 4)
              (none : Option Bool) =
            List.append
              (List.replicate (4 * rest.length)
                (none : Option Bool))
              ([none, none, none, none] : List (Option Bool)) := by
        simp [List.replicate_succ', List.append_assoc]
      rw [hrep]
      simp [List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked_to_tail
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (8 * w.length + 4)
        (projectionConfig 367 leftRev
          (List.append (projectionAllMarkedBoolWordCells w) tail)) =
      projectionConfig 380
        (List.append (List.replicate (4 * w.length) none)
          (List.append [none, none, none, none]
            (List.append (List.replicate (4 * w.length) none)
              leftRev))) tail := by
  have hsteps :
      8 * w.length + 4 =
        4 * w.length + (4 + 4 * w.length) := by
    omega
  rw [hsteps, MachineDescription.runConfig_add]
  change DovetailControllerStageInputProjectionDescription.runConfig
      (4 + 4 * w.length)
      (DovetailControllerStageInputProjectionDescription.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (List.append (projectionAllMarkedBoolWordCells w) tail))) = _
  simp [projectionAllMarkedBoolWordCells, List.append_assoc]
  change DovetailControllerStageInputProjectionDescription.runConfig
      (4 + 4 * w.length)
      (DovetailControllerStageInputProjectionDescription.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells w.length)
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells w) tail))))) = _
  have hticks :=
    dovetailControllerStageInputProjectionDescription_run_cleanup_marked_ticks
      (count := w.length) (leftRev := leftRev)
      (tail := List.append projectionDoneCodeCells
        (List.append (projectionMarkedBoolPayloadCells w) tail))
  rw [hticks]
  rw [show 4 + 4 * w.length = 4 + 4 * w.length by rfl,
    MachineDescription.runConfig_add]
  change DovetailControllerStageInputProjectionDescription.runConfig
      (4 * w.length)
      (DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 367
          (List.append (List.replicate (4 * w.length) none) leftRev)
          (List.append projectionDoneCodeCells
            (List.append (projectionMarkedBoolPayloadCells w) tail)))) = _
  rw [dovetailControllerStageInputProjectionDescription_run_cleanup_done]
  rw [dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload_to_tail]
  simp

private theorem dovetailControllerStageInputProjectionDescription_state_ne_halt_of_stepConfig_none
    {c : MachineDescription.Configuration} {n : Nat}
    (hstep :
      DovetailControllerStageInputProjectionDescription.stepConfig c = none)
    (hstate : c.state ≠ DovetailControllerStageInputProjectionDescription.halt) :
    (DovetailControllerStageInputProjectionDescription.runConfig n c).state ≠
      DovetailControllerStageInputProjectionDescription.halt := by
  have hrun :=
    MachineDescription.runConfig_of_stepConfig_none
      (D := DovetailControllerStageInputProjectionDescription)
      hstep n
  rw [hrun]
  exact hstate

private theorem dovetailControllerStageInputProjectionDescription_run_state380_true_ne_halt
    (leftRev tail : List (Option Bool)) (n : Nat) :
    (DovetailControllerStageInputProjectionDescription.runConfig n
      (projectionConfig 380 leftRev (some true :: tail))).state ≠
      DovetailControllerStageInputProjectionDescription.halt := by
  apply
    dovetailControllerStageInputProjectionDescription_state_ne_halt_of_stepConfig_none
  · rfl
  · simp [projectionConfig, DovetailControllerStageInputProjectionDescription]

private theorem dovetailControllerStageInputProjectionDescription_run_state381_nonblank_ne_halt
    (b : Bool) (leftRev tail : List (Option Bool)) (n : Nat) :
    (DovetailControllerStageInputProjectionDescription.runConfig n
      (projectionConfig 381 leftRev (some b :: tail))).state ≠
      DovetailControllerStageInputProjectionDescription.halt := by
  apply
    dovetailControllerStageInputProjectionDescription_state_ne_halt_of_stepConfig_none
  · cases b <;> rfl
  · simp [projectionConfig, DovetailControllerStageInputProjectionDescription]

private theorem dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
    (b : Bool) (leftRev tail : List (Option Bool)) (n : Nat) :
    (DovetailControllerStageInputProjectionDescription.runConfig (n + 1)
      (projectionConfig 380 leftRev (some false :: some b :: tail))).state ≠
      DovetailControllerStageInputProjectionDescription.halt := by
  change
    (DovetailControllerStageInputProjectionDescription.runConfig n
      (projectionConfig 381 (none :: leftRev) (some b :: tail))).state ≠
      DovetailControllerStageInputProjectionDescription.halt
  exact
    dovetailControllerStageInputProjectionDescription_run_state381_nonblank_ne_halt
      b (none :: leftRev) tail n

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_code_suffix_ne_halt
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (DovetailControllerStageInputProjectionDescription.runConfig n
      (projectionConfig 380 leftRev
        (projectionCodeCells (symbol :: suffix)))).state ≠
      DovetailControllerStageInputProjectionDescription.halt := by
  cases n with
  | zero =>
      change (380 : Nat) ≠ 999
      omega
  | succ n =>
      cases symbol <;>
        simp [projectionCodeCells, MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput]
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some false :: some false ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some false :: some true ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some true :: some false ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some true :: some true ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some false :: some false ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some false :: some true ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some true :: some false ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some true :: some true ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            n
      · exact
          dovetailControllerStageInputProjectionDescription_run_state380_true_ne_halt
            leftRev
            (some false :: some false :: some false ::
              List.map some (MachineDescription.encodeCodeWordAsInput suffix))
            (n + 1)

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked_code_suffix_after_prefix_ne_halt
    (w : Word Bool) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (DovetailControllerStageInputProjectionDescription.runConfig
      (8 * w.length + 4 + n)
      (projectionConfig 367 leftRev
        (List.append (projectionAllMarkedBoolWordCells w)
          (projectionCodeCells (symbol :: suffix))))).state ≠
      DovetailControllerStageInputProjectionDescription.halt := by
  rw [show 8 * w.length + 4 + n = (8 * w.length + 4) + n by omega,
    MachineDescription.runConfig_add]
  rw [dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked_to_tail]
  exact
    dovetailControllerStageInputProjectionDescription_run_cleanup_code_suffix_ne_halt
      symbol suffix
      (List.append (List.replicate (4 * w.length) none)
        (List.append [none, none, none, none]
          (List.append (List.replicate (4 * w.length) none) leftRev)))
      n

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked
    (w : Word Bool) (leftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (8 * w.length + 5)
        (projectionConfig 367 leftRev
          (projectionAllMarkedBoolWordCells w)) =
      projectionConfig 999
        (List.append (List.replicate (4 * w.length + 1) none)
          (List.append [none, none, none, none]
            (List.append (List.replicate (4 * w.length) none)
              leftRev))) [] := by
  have hsteps :
      8 * w.length + 5 =
        4 * w.length + (4 + (4 * w.length + 1)) := by
    omega
  rw [hsteps, MachineDescription.runConfig_add]
  change DovetailControllerStageInputProjectionDescription.runConfig
      (4 + (4 * w.length + 1))
      (DovetailControllerStageInputProjectionDescription.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (projectionAllMarkedBoolWordCells w))) = _
  simp [projectionAllMarkedBoolWordCells]
  change DovetailControllerStageInputProjectionDescription.runConfig
      (4 + (4 * w.length + 1))
      (DovetailControllerStageInputProjectionDescription.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells w.length)
            (List.append projectionDoneCodeCells
              (projectionMarkedBoolPayloadCells w))))) = _
  rw [dovetailControllerStageInputProjectionDescription_run_cleanup_marked_ticks
    (count := w.length) (leftRev := leftRev)
    (tail := List.append projectionDoneCodeCells
      (projectionMarkedBoolPayloadCells w))]
  rw [show 4 + (4 * w.length + 1) = 4 + (4 * w.length + 1) by rfl,
    MachineDescription.runConfig_add]
  change DovetailControllerStageInputProjectionDescription.runConfig
      (4 * w.length + 1)
      (DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 367
          (List.append (List.replicate (4 * w.length) none) leftRev)
          (List.append projectionDoneCodeCells
            (projectionMarkedBoolPayloadCells w)))) = _
  rw [dovetailControllerStageInputProjectionDescription_run_cleanup_done]
  rw [dovetailControllerStageInputProjectionDescription_run_cleanup_marked_payload]
  simp

private theorem dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked_code_suffix_fixed_halt_iff
    (w : Word Bool) (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) :
    (DovetailControllerStageInputProjectionDescription.runConfig
      (8 * w.length + 5)
      (projectionConfig 367 leftRev
        (List.append (projectionAllMarkedBoolWordCells w)
          (projectionCodeCells suffix)))).state =
        DovetailControllerStageInputProjectionDescription.halt <->
      suffix = [] := by
  constructor
  · intro h
    cases suffix with
    | nil =>
        rfl
    | cons symbol rest =>
        exact False.elim
          (dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked_code_suffix_after_prefix_ne_halt
            w symbol rest leftRev 1 h)
  · intro h
    subst suffix
    simp [projectionCodeCells, MachineDescription.encodeCodeWordAsInput]
    rw [dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked]
    rfl

private def projectionScanState140 : Nat -> Nat
  | 0 => 140
  | 1 => 141
  | 2 => 142
  | _ => 143

private def projectionScanCountStep (count : Nat) :
    Option Bool -> Nat
  | some _ => 0
  | none =>
      match count with
      | 0 => 1
      | 1 => 2
      | _ => 3

private def projectionScanCountFold : Nat -> List (Option Bool) -> Nat
  | count, [] => count
  | count, cell :: rest =>
      projectionScanCountFold (projectionScanCountStep count cell) rest

private def projectionScanSafe : Nat -> List (Option Bool) -> Prop
  | _, [] => True
  | count, cell :: rest =>
      (count ≠ 3 ∨ cell ≠ none) ∧
        projectionScanSafe (projectionScanCountStep count cell) rest

private def projectionScanLeftConfig
    (state : Nat) (leftOfBoundary : List (Option Bool))
    (boundaryHead : Option Bool) :
    List (Option Bool) -> List (Option Bool) ->
      MachineDescription.Configuration
  | [], tail =>
      projectionConfig state leftOfBoundary (boundaryHead :: tail)
  | cell :: rest, tail =>
      projectionConfig state
        (List.append rest (boundaryHead :: leftOfBoundary)) (cell :: tail)

private theorem projectionScanCountStep_le_three
    {count : Nat} (hcount : count ≤ 3) (cell : Option Bool) :
    projectionScanCountStep count cell ≤ 3 := by
  cases cell with
  | none =>
      cases count with
      | zero =>
          simp [projectionScanCountStep]
      | succ count =>
          cases count with
          | zero =>
              simp [projectionScanCountStep]
          | succ count =>
              simp [projectionScanCountStep]
  | some b =>
      cases b <;> simp [projectionScanCountStep]

private theorem dovetailControllerStageInputProjectionDescription_run_scan140_step
    (count : Nat) (hcount : count ≤ 3)
    (cell : Option Bool) (rest leftOfBoundary tail : List (Option Bool))
    (boundaryHead : Option Bool)
    (hsafe : count ≠ 3 ∨ cell ≠ none) :
    DovetailControllerStageInputProjectionDescription.runConfig 1
        (projectionScanLeftConfig (projectionScanState140 count)
          leftOfBoundary boundaryHead (cell :: rest) tail) =
      projectionScanLeftConfig
        (projectionScanState140 (projectionScanCountStep count cell))
        leftOfBoundary boundaryHead rest (cell :: tail) := by
  cases rest with
  | nil =>
      cases count with
      | zero =>
          cases cell with
          | none =>
              rfl
          | some b =>
              cases b <;> rfl
      | succ count =>
          cases count with
          | zero =>
              cases cell with
              | none =>
                  rfl
              | some b =>
                  cases b <;> rfl
          | succ count =>
              cases count with
              | zero =>
                  cases cell with
                  | none =>
                      rfl
                  | some b =>
                      cases b <;> rfl
              | succ count =>
                  cases count with
                  | zero =>
                      cases cell with
                      | none =>
                          exact False.elim
                            (hsafe.elim (fun h => h rfl) (fun h => h rfl))
                      | some b =>
                          cases b <;> rfl
                  | succ count =>
                      have hfalse : False := by omega
                      exact False.elim hfalse
  | cons next more =>
      cases count with
      | zero =>
          cases cell with
          | none =>
              rfl
          | some b =>
              cases b <;> rfl
      | succ count =>
          cases count with
          | zero =>
              cases cell with
              | none =>
                  rfl
              | some b =>
                  cases b <;> rfl
          | succ count =>
              cases count with
              | zero =>
                  cases cell with
                  | none =>
                      rfl
                  | some b =>
                      cases b <;> rfl
              | succ count =>
                  cases count with
                  | zero =>
                      cases cell with
                      | none =>
                          exact False.elim
                            (hsafe.elim (fun h => h rfl) (fun h => h rfl))
                      | some b =>
                          cases b <;> rfl
                  | succ count =>
                      have hfalse : False := by omega
                      exact False.elim hfalse

private theorem dovetailControllerStageInputProjectionDescription_run_scan140_cells
    (cellsRev : List (Option Bool)) (count : Nat) (hcount : count ≤ 3)
    (hsafe : projectionScanSafe count cellsRev)
    (leftOfBoundary : List (Option Bool)) (boundaryHead : Option Bool)
    (tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig cellsRev.length
        (projectionScanLeftConfig (projectionScanState140 count)
          leftOfBoundary boundaryHead cellsRev tail) =
      projectionConfig
        (projectionScanState140
          (projectionScanCountFold count cellsRev))
        leftOfBoundary
        (boundaryHead :: List.append cellsRev.reverse tail) := by
  induction cellsRev generalizing count tail with
  | nil =>
      rfl
  | cons cell rest ih =>
      rcases hsafe with ⟨hcell, hrest⟩
      have hnext :
          projectionScanCountStep count cell ≤ 3 :=
        projectionScanCountStep_le_three hcount cell
      rw [show (cell :: rest).length = 1 + rest.length by
        simp
        omega,
        MachineDescription.runConfig_add]
      change
        DovetailControllerStageInputProjectionDescription.runConfig
            rest.length
            (DovetailControllerStageInputProjectionDescription.runConfig 1
              (projectionScanLeftConfig (projectionScanState140 count)
                leftOfBoundary boundaryHead (cell :: rest) tail)) =
          projectionConfig
            (projectionScanState140
              (projectionScanCountFold count (cell :: rest)))
            leftOfBoundary
            (boundaryHead :: List.append (cell :: rest).reverse tail)
      rw [dovetailControllerStageInputProjectionDescription_run_scan140_step
        count hcount cell rest leftOfBoundary tail boundaryHead hcell]
      rw [ih (projectionScanCountStep count cell) hnext hrest
        (cell :: tail)]
      simp [projectionScanCountFold, List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_scan140_boundary
    (base tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 7
        (projectionConfig 140 (none :: none :: none :: base) (none :: tail)) =
      projectionConfig 100
        (List.append [none, none, none, none] base) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_scan140_cells_to_boundary
    (cellsRev : List (Option Bool))
    (hsafe : projectionScanSafe 0 cellsRev)
    (hcount : projectionScanCountFold 0 cellsRev = 0)
    (base tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (cellsRev.length + 7)
        (projectionScanLeftConfig 140
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail) =
      projectionConfig 100
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail) := by
  rw [MachineDescription.runConfig_add]
  change
    DovetailControllerStageInputProjectionDescription.runConfig 7
        (DovetailControllerStageInputProjectionDescription.runConfig
        cellsRev.length
        (projectionScanLeftConfig (projectionScanState140 0)
          (List.append ([none, none, none] : List (Option Bool)) base) none
          cellsRev tail)) =
      projectionConfig 100
        (List.append [none, none, none, none] base)
        (List.append cellsRev.reverse tail)
  rw [dovetailControllerStageInputProjectionDescription_run_scan140_cells
    cellsRev 0 (by omega) hsafe
    (List.append ([none, none, none] : List (Option Bool)) base) none tail]
  rw [hcount]
  simpa [List.append_assoc] using
    dovetailControllerStageInputProjectionDescription_run_scan140_boundary
      base (List.append cellsRev.reverse tail)

private theorem dovetailControllerStageInputProjectionDescription_run_state100_marked_tick
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 100 leftRev
          (List.append projectionMarkedTickCodeCells tail)) =
      projectionConfig 100
        (List.append projectionMarkedTickCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_state100_marked_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig (4 * count)
        (projectionConfig 100 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells count)
            tail)) =
      projectionConfig 100
        (List.append
          (projectionRepeatedCells projectionMarkedTickCodeCells count).reverse
          leftRev)
        tail := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      have hsteps : 4 * (count + 1) = 4 + 4 * count := by omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * count)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 100 leftRev
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  (count + 1)) tail))) = _
      rw [show projectionRepeatedCells projectionMarkedTickCodeCells
          (count + 1) =
          List.append projectionMarkedTickCodeCells
            (projectionRepeatedCells projectionMarkedTickCodeCells count) by
        rfl]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * count)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 100 leftRev
              (List.append projectionMarkedTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells count)
                  tail)))) = _
      rw [dovetailControllerStageInputProjectionDescription_run_state100_marked_tick]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_state100_mark_tick
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 100 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 120
        (List.append projectionMarkedTickCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_state120_tick
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 120 leftRev
          (List.append projectionTickCodeCells tail)) =
      projectionConfig 120
        (List.append projectionTickCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_state120_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig (4 * count)
        (projectionConfig 120 leftRev
          (List.append
            (projectionRepeatedCells projectionTickCodeCells count)
            tail)) =
      projectionConfig 120
        (List.append
          (projectionRepeatedCells projectionTickCodeCells count).reverse
          leftRev)
        tail := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      have hsteps : 4 * (count + 1) = 4 + 4 * count := by omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * count)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 120 leftRev
              (List.append
                (projectionRepeatedCells projectionTickCodeCells
                  (count + 1)) tail))) = _
      rw [show projectionRepeatedCells projectionTickCodeCells
          (count + 1) =
          List.append projectionTickCodeCells
            (projectionRepeatedCells projectionTickCodeCells count) by
        rfl]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * count)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 120 leftRev
              (List.append projectionTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionTickCodeCells count)
                  tail)))) = _
      rw [dovetailControllerStageInputProjectionDescription_run_state120_tick]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

private theorem dovetailControllerStageInputProjectionDescription_run_state120_done
    (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 120 leftRev
          (List.append projectionDoneCodeCells tail)) =
      projectionConfig 130
        (List.append projectionDoneCodeCells.reverse leftRev) tail := by
  cases tail with
  | nil =>
      rfl
  | cons cell rest =>
      cases cell with
      | none =>
          rfl
      | some b =>
          cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_state130_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 130 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) tail)) =
      projectionConfig 130
        (List.append (projectionMarkedBoolCellCodeCells b).reverse leftRev)
        tail := by
  cases b <;>
    cases tail with
    | nil =>
        rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_state130_marked_payload_cell_append
    (b : Bool) (leftRev middle tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 130 leftRev
          (List.append (projectionMarkedBoolCellCodeCells b) middle ++
            tail)) =
      projectionConfig 130
        (List.append (projectionMarkedBoolCellCodeCells b).reverse leftRev)
        (List.append middle tail) := by
  cases b <;>
    cases middle with
    | nil =>
        cases tail with
        | nil =>
            rfl
        | cons cell rest =>
            cases cell with
            | none =>
                rfl
            | some b =>
                cases b <;> rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

private theorem dovetailControllerStageInputProjectionDescription_run_state130_marked_payload
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig (4 * w.length)
        (projectionConfig 130 leftRev
          (List.append (projectionMarkedBoolPayloadCells w) tail)) =
      projectionConfig 130
        (List.append (projectionMarkedBoolPayloadCells w).reverse leftRev)
        tail := by
  induction w generalizing leftRev with
  | nil =>
      rfl
  | cons b rest ih =>
      have hsteps : 4 * (b :: rest).length = 4 + 4 * rest.length := by
        simp
        omega
      rw [hsteps, MachineDescription.runConfig_add]
      change DovetailControllerStageInputProjectionDescription.runConfig
          (4 * rest.length)
          (DovetailControllerStageInputProjectionDescription.runConfig 4
            (projectionConfig 130 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest) ++ tail))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [dovetailControllerStageInputProjectionDescription_run_state130_marked_payload_cell_append]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

private def projectionMarkedBoolCellScanPrefixRev (b : Bool) :
    List (Option Bool) :=
  match b with
  | false => [some false, none, some false]
  | true => [some true, none, some false]

private def projectionMarkedBoolCellScanTailHead (b : Bool) :
    Option Bool :=
  match b with
  | false => some true
  | true => some false

private theorem dovetailControllerStageInputProjectionDescription_run_state130_mark_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig 4
        (projectionConfig 130 leftRev
          (List.append (projectionBoolCellCodeCells b) tail)) =
      projectionConfig 140 (none :: some false :: leftRev)
        (List.append
          (match b with
          | false => [some false, some true]
          | true => [some true, some false])
          tail) := by
  cases b <;>
    cases tail with
    | nil =>
        rfl
    | cons cell rest =>
        cases cell with
        | none =>
            rfl
        | some b =>
            cases b <;> rfl

private def projectionInputMarkPreviousCells
    (marked rest : Word Bool) : List (Option Bool) :=
  List.append
    (projectionRepeatedCells projectionMarkedTickCodeCells
      (marked.length + 1))
    (List.append
      (projectionCodeCells (List.replicate rest.length
        MachineCodeSymbol.tick))
      (List.append projectionDoneCodeCells
        (projectionMarkedBoolPayloadCells marked)))

private def projectionInputMarkScanBackCellsRev
    (marked rest : Word Bool) (b : Bool) : List (Option Bool) :=
  List.append (projectionMarkedBoolCellScanPrefixRev b)
    (projectionInputMarkPreviousCells marked rest).reverse

private def projectionInputMarkScanTail
    (rest : Word Bool) (b : Bool) (suffix : Word MachineCodeSymbol) :
    List (Option Bool) :=
  projectionMarkedBoolCellScanTailHead b ::
    List.append (projectionBoolPayloadCells rest) (projectionCodeCells suffix)

private def projectionInputBoolWordCost (w : Word Bool) : Nat :=
  12 * w.length * w.length + 42 * w.length + 24

private def projectionResultBoolWordCost (w : Word Bool) : Nat :=
  12 * w.length * w.length + 34 * w.length + 16

private def projectionInputMarkStepCost
    (marked rest : Word Bool) : Nat :=
  16 * marked.length + 8 * rest.length + 30

private def projectionInputRemainingCost
    (marked rest : Word Bool) : Nat :=
  12 * rest.length * rest.length +
    16 * marked.length * rest.length +
    42 * rest.length + 24 * marked.length + 24

private theorem dovetailControllerStageInputProjectionDescription_run_input_mark_one
    (marked rest : Word Bool) (b : Bool)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (projectionInputMarkStepCost marked rest)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked (b :: rest) suffix)) =
      projectionConfig 100
        (List.append [none, none, none, none] baseLeftRev)
        (projectionBoolWordWorkCells (List.append marked [b]) rest suffix) := by
  sorry

private theorem dovetailControllerStageInputProjectionDescription_run_input_finish_marked
    (marked : Word Bool) (stage : Nat) (result : Word Bool)
    (baseLeftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (24 * marked.length + 24)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked []
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeBoolWord result)))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord marked)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeBoolWord result))) := by
  induction marked generalizing baseLeftRev with
  | nil =>
      cases stage <;> rfl
  | cons b rest ih =>
      sorry

private theorem dovetailControllerStageInputProjectionDescription_run_input_bool_word_acc
    (marked rest : Word Bool) (stage : Nat) (result : Word Bool)
    (baseLeftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (projectionInputRemainingCost marked rest)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked rest
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeBoolWord result)))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells
            (MachineDescription.encodeBoolWord
              (List.append marked rest))).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeBoolWord result))) := by
  induction rest generalizing marked baseLeftRev with
  | nil =>
      simp [projectionInputRemainingCost]
      exact
        dovetailControllerStageInputProjectionDescription_run_input_finish_marked
          marked stage result baseLeftRev
  | cons b rest ih =>
      have hcost :
          projectionInputRemainingCost marked (b :: rest) =
            projectionInputMarkStepCost marked rest +
              projectionInputRemainingCost (List.append marked [b]) rest := by
        simp [projectionInputRemainingCost, projectionInputMarkStepCost,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hcost, MachineDescription.runConfig_add]
      rw [dovetailControllerStageInputProjectionDescription_run_input_mark_one]
      rw [ih]
      have hword :
          List.append (List.append marked [b]) rest =
            List.append marked (b :: rest) := by
        simp [List.append_assoc]
      rw [hword]

private theorem dovetailControllerStageInputProjectionDescription_run_input_bool_word
    (w : Word Bool) (stage : Nat) (result : Word Bool)
    (baseLeftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (projectionInputBoolWordCost w)
        (projectionConfig 100
          (List.append [none, none, none, none] baseLeftRev)
          (projectionCodeCells
            (MachineDescription.encodeBoolWordAppend w
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeBoolWord result))))) =
      projectionConfig 200
        (List.append
          (projectionCodeCells (MachineDescription.encodeBoolWord w)).reverse
          (List.append [none, none, none, none] baseLeftRev))
        (projectionCodeCells
          (MachineDescription.encodeNatAppend stage
            (MachineDescription.encodeBoolWord result))) := by
  have h :=
    dovetailControllerStageInputProjectionDescription_run_input_bool_word_acc
      ([] : Word Bool) w stage result baseLeftRev
  simpa [projectionInputRemainingCost, projectionInputBoolWordCost,
    projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h

private theorem dovetailControllerStageInputProjectionDescription_run_result_bool_word
    (w : Word Bool) (baseLeftRev : List (Option Bool)) :
    DovetailControllerStageInputProjectionDescription.runConfig
        (projectionResultBoolWordCost w)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionCodeCells (MachineDescription.encodeBoolWord w))) =
      projectionConfig 367
        (List.append projectionDoneCodeCells.reverse baseLeftRev)
        (projectionAllMarkedBoolWordCells w) := by
  sorry

private theorem dovetailControllerStageInputProjectionDescription_final_normalizedOutput
    (input result : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (projectionTapeAtCells
          (List.append (List.replicate (4 * result.length + 1) none)
            (List.append [none, none, none, none]
              (List.append (List.replicate (4 * result.length) none)
                (List.append projectionDoneCodeCells.reverse
                  (List.append (projectionStageTickCellsRev stage)
                    (List.append
                      (projectionCodeCells
                        (MachineDescription.encodeBoolWord input)).reverse
                      [none, none, none, none])))))) []) =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.stageInputCode input stage) := by
  simp [Tape.normalizedOutput, Tape.cells, projectionTapeAtCells,
    MachineDescription.DovetailLayout.stageInputCode,
    MachineDescription.DovetailLayout.stageInputCodeAppend,
    projectionStageTickCellsRev, projectionCodeCells_filterMap,
    projectionDoneCodeCells_filterMap]
  rw [encodeCodeWordAsInput_encodeBoolWordAppend]
  simp [MachineDescription.encodeNatAppend]
  rw [encodeCodeWordAsInput_encodeNat]
  simp

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_encode
    (C : MachineDescription.DovetailControllerLayout) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.stageInputCode C)) := by
  rcases C with ⟨input, stage, result⟩
  let inputLeftRev :=
    List.append
      (projectionCodeCells (MachineDescription.encodeBoolWord input)).reverse
      ([none, none, none, none] : List (Option Bool))
  let stageLeftRev :=
    List.append [none, none, none, none]
      (List.append (projectionStageTickCellsRev stage) inputLeftRev)
  let finalLeftRev :=
    List.append (List.replicate (4 * result.length + 1) none)
      (List.append [none, none, none, none]
        (List.append (List.replicate (4 * result.length) none)
          (List.append projectionDoneCodeCells.reverse
            (List.append (projectionStageTickCellsRev stage) inputLeftRev))))
  have hrun :
      DovetailControllerStageInputProjectionDescription.runConfig
          (4 + projectionInputBoolWordCost input + (4 * stage + 12) +
            projectionResultBoolWordCost result + (8 * result.length + 5))
          (DovetailControllerStageInputProjectionDescription.initial
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                { input := input, stage := stage, result := result }))) =
        projectionConfig 999 finalLeftRev [] := by
    rw [show
        4 + projectionInputBoolWordCost input + (4 * stage + 12) +
              projectionResultBoolWordCost result +
              (8 * result.length + 5) =
            4 +
              (projectionInputBoolWordCost input +
                ((4 * stage + 12) +
                  (projectionResultBoolWordCost result +
                    (8 * result.length + 5)))) by
        omega]
    rw [MachineDescription.runConfig_add]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (DovetailControllerStageInputProjectionDescription.runConfig 4
          (DovetailControllerStageInputProjectionDescription.initial
            (MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailControllerLayout.encode
                { input := input, stage := stage, result := result })))) =
        projectionConfig 999 finalLeftRev []
    simp [MachineDescription.DovetailControllerLayout.encode,
      MachineDescription.DovetailControllerLayout.encodeAppend,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (DovetailControllerStageInputProjectionDescription.runConfig 4
          (DovetailControllerStageInputProjectionDescription.initial
            (List.append [false, false, false, false]
              (MachineDescription.encodeCodeWordAsInput
                (MachineDescription.DovetailLayout.stageInputCodeAppend input
                  stage (MachineDescription.encodeBoolWordAppend result [])))))) =
        projectionConfig 999 finalLeftRev []
    rw [dovetailControllerStageInputProjectionDescription_run_header]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (projectionInputBoolWordCost input +
          ((4 * stage + 12) +
            (projectionResultBoolWordCost result +
              (8 * result.length + 5))))
        (projectionConfig 100 [none, none, none, none]
          (projectionCodeCells
            (MachineDescription.DovetailLayout.stageInputCodeAppend input stage
              (MachineDescription.encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    simp [MachineDescription.DovetailLayout.stageInputCodeAppend]
    rw [MachineDescription.runConfig_add]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        ((4 * stage + 12) +
          (projectionResultBoolWordCost result + (8 * result.length + 5)))
        (DovetailControllerStageInputProjectionDescription.runConfig
          (projectionInputBoolWordCost input)
          (projectionConfig 100
            (List.append [none, none, none, none]
              ([] : List (Option Bool)))
            (projectionCodeCells
              (MachineDescription.encodeBoolWordAppend input
                (MachineDescription.encodeNatAppend stage
                  (MachineDescription.encodeBoolWord result)))))) =
        projectionConfig 999 finalLeftRev []
    rw [dovetailControllerStageInputProjectionDescription_run_input_bool_word
      (stage := stage) (result := result) (baseLeftRev := [])]
    rw [MachineDescription.runConfig_add]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (DovetailControllerStageInputProjectionDescription.runConfig
          (4 * stage + 12)
          (projectionConfig 200 inputLeftRev
            (projectionCodeCells
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeBoolWord result))))) =
        projectionConfig 999 finalLeftRev []
    rw [dovetailControllerStageInputProjectionDescription_run_stage_nat]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (projectionResultBoolWordCost result + (8 * result.length + 5))
        (projectionConfig 300 stageLeftRev
          (projectionCodeCells (MachineDescription.encodeBoolWord result))) =
        projectionConfig 999 finalLeftRev []
    rw [MachineDescription.runConfig_add]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (8 * result.length + 5)
        (DovetailControllerStageInputProjectionDescription.runConfig
          (projectionResultBoolWordCost result)
          (projectionConfig 300
            (List.append [none, none, none, none]
              (List.append (projectionStageTickCellsRev stage) inputLeftRev))
            (projectionCodeCells
              (MachineDescription.encodeBoolWord result)))) =
        projectionConfig 999 finalLeftRev []
    rw [dovetailControllerStageInputProjectionDescription_run_result_bool_word]
    change
      DovetailControllerStageInputProjectionDescription.runConfig
        (8 * result.length + 5)
        (projectionConfig 367
          (List.append projectionDoneCodeCells.reverse
            (List.append (projectionStageTickCellsRev stage) inputLeftRev))
          (projectionAllMarkedBoolWordCells result)) =
        projectionConfig 999 finalLeftRev []
    rw [dovetailControllerStageInputProjectionDescription_run_cleanup_all_marked]
  refine
    ⟨4 + projectionInputBoolWordCost input + (4 * stage + 12) +
        projectionResultBoolWordCost result + (8 * result.length + 5), ?_⟩
  constructor
  · rw [hrun]
    rfl
  · rw [hrun]
    change
      Tape.normalizedOutput
          (projectionTapeAtCells finalLeftRev []) =
        MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.stageInputCode
            { input := input, stage := stage, result := result })
    simpa [finalLeftRev, inputLeftRev,
      MachineDescription.DovetailControllerLayout.stageInputCode] using
        dovetailControllerStageInputProjectionDescription_final_normalizedOutput
          input result stage

private theorem dovetailControllerStageInputProjectionDescription_decodeComplete_of_halting_run
    {code : Word MachineCodeSymbol} {n : Nat}
    (hstate :
      (DovetailControllerStageInputProjectionDescription.runConfig n
        (DovetailControllerStageInputProjectionDescription.initial
          (MachineDescription.encodeCodeWordAsInput code))).state =
        DovetailControllerStageInputProjectionDescription.halt) :
    exists C : MachineDescription.DovetailControllerLayout,
      MachineDescription.DovetailControllerLayout.decodeComplete code =
        some C := by
  sorry

theorem dovetailControllerStageInputProjectionDescription_decodeComplete_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    exists C : MachineDescription.DovetailControllerLayout,
      MachineDescription.DovetailControllerLayout.decodeComplete code =
        some C := by
  rcases h with ⟨n, hn⟩
  exact
    dovetailControllerStageInputProjectionDescription_decodeComplete_of_halting_run
      (code := code) (n := n) hn.left

theorem dovetailControllerStageInputProjectionDescription_exists_layout_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    exists C : MachineDescription.DovetailControllerLayout,
      code = MachineDescription.DovetailControllerLayout.encode C ∧
        out = MachineDescription.DovetailControllerLayout.stageInputCode C := by
  rcases
    dovetailControllerStageInputProjectionDescription_decodeComplete_of_haltsWithOutput
      h with
    ⟨C, hdecode⟩
  have hcode :
      code = MachineDescription.DovetailControllerLayout.encode C :=
    MachineDescription.DovetailControllerLayout.decodeComplete_eq_some_encode
      hdecode
  subst code
  have hsuccess :=
    dovetailControllerStageInputProjectionDescription_haltsWithOutput_encode C
  have hbits :
      MachineDescription.encodeCodeWordAsInput out =
        MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.stageInputCode C) :=
    MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
      dovetailControllerStageInputProjectionDescription_haltTransitionFree
      h hsuccess
  have hout :
      out = MachineDescription.DovetailControllerLayout.stageInputCode C :=
    MachineDescription.encodeCodeWordAsInput_injective hbits
  exact ⟨C, rfl, hout⟩

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff_exists_layout
    (code out : Word MachineCodeSymbol) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      exists C : MachineDescription.DovetailControllerLayout,
        code = MachineDescription.DovetailControllerLayout.encode C ∧
          out = MachineDescription.DovetailControllerLayout.stageInputCode C := by
  constructor
  · intro h
    exact
      dovetailControllerStageInputProjectionDescription_exists_layout_of_haltsWithOutput
        h
  · intro h
    rcases h with ⟨C, rfl, rfl⟩
    exact
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_encode C

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_of_transform_eq_some
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
          code = some out) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) := by
  have hparsed :=
    (pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
      code out).mp h
  exact
    (dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff_exists_layout
      code out).mpr hparsed

theorem dovetailControllerStageInputProjectionDescription_transform_eq_some_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  have hparsed :=
    (dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff_exists_layout
      code out).mp h
  exact
    (pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
      code out).mpr hparsed

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff
    (code out : Word MachineCodeSymbol) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  constructor
  · exact
      dovetailControllerStageInputProjectionDescription_transform_eq_some_of_haltsWithOutput
  · exact
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_of_transform_eq_some

theorem dovetailControllerStageInputProjectionDescription_outputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      DovetailControllerStageInputProjectionDescription :=
  ⟨⟨dovetailControllerStageInputProjectionDescription_wellFormed,
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff⟩,
    dovetailControllerStageInputProjectionDescription_haltTransitionFree⟩

theorem encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold :
    EncodedControllerStageInputProjectionCodeWordSubroutineConstruction := by
  exact
    ⟨DovetailControllerStageInputProjectionDescription,
      dovetailControllerStageInputProjectionDescription_outputCompiledSubroutine⟩

end Computability
end FoC

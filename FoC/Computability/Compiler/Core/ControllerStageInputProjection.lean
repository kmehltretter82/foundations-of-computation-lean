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

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_encode
    (C : MachineDescription.DovetailControllerLayout) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.encode C))
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailControllerLayout.stageInputCode C)) := by
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
  sorry

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

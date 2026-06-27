import FoC.Computability.Compiler.Core.EncodedRewriters
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.TransitionTableChecks

set_option doc.verso true

/-!
# Controller stage-input projection machine
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerStageInputProjection

def keep
    (source : Nat) (cell : Bool) (target : Nat) :
    TransitionDescription :=
  transition source (some cell) (some cell)
    Direction.right target

def erase
    (source : Nat) (cell : Option Bool) (target : Nat) :
    TransitionDescription :=
  transition source cell none Direction.right target

def keepMove
    (source : Nat) (cell : Option Bool) (move : Direction) (target : Nat) :
    TransitionDescription :=
  transition source cell cell move target

def writeMove
    (source : Nat) (read write : Option Bool) (move : Direction)
    (target : Nat) : TransitionDescription :=
  transition source read write move target

def scanLeftToBoundary
    (scan one two three found : Nat) : List TransitionDescription :=
  [ keepMove scan none Direction.left one
  , keepMove scan (some false) Direction.left scan
  , keepMove scan (some true) Direction.left scan
  , keepMove one none Direction.left two
  , keepMove one (some false) Direction.left scan
  , keepMove one (some true) Direction.left scan
  , keepMove two none Direction.left three
  , keepMove two (some false) Direction.left scan
  , keepMove two (some true) Direction.left scan
  , keepMove three none Direction.right found
  , keepMove three (some false) Direction.left scan
  , keepMove three (some true) Direction.left scan ]

def projectionTapeAtCells
    (leftRev : List (Option Bool)) : List (Option Bool) -> Tape Bool
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

def projectionTapeAt
    (leftRev : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  projectionTapeAtCells leftRev (bits.map some)

def projectionConfig
    (state : Nat) (leftRev cells : List (Option Bool)) :
    Configuration :=
  { state := state, tape := projectionTapeAtCells leftRev cells }

def projectionCodeCells
    (code : Word MachineCodeSymbol) : List (Option Bool) :=
  (encodeCodeWordAsInput code).map some

def projectionTickCodeCells : List (Option Bool) :=
  (encodeCodeSymbolAsInput MachineCodeSymbol.tick).map some

def projectionTickCodeCellsRev : List (Option Bool) :=
  projectionTickCodeCells.reverse

def projectionDoneCodeCells : List (Option Bool) :=
  (encodeCodeSymbolAsInput MachineCodeSymbol.done).map some

def projectionMarkedTickCodeCells : List (Option Bool) :=
  [some false, some false, some true, none]

def projectionBoolCellCodeCells (b : Bool) : List (Option Bool) :=
  (encodeCodeSymbolAsInput
    (if b then MachineCodeSymbol.one else MachineCodeSymbol.zero)).map some

def projectionMarkedBoolCellCodeCells : Bool -> List (Option Bool)
  | false => [some false, none, some false, some true]
  | true => [some false, none, some true, some false]

def projectionRepeatedCells
    (chunk : List (Option Bool)) : Nat -> List (Option Bool)
  | 0 => []
  | n + 1 => List.append chunk (projectionRepeatedCells chunk n)

theorem projectionRepeatedCells_succ_right
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

theorem projectionRepeatedCells_append_self_comm
    (chunk : List (Option Bool)) (n : Nat) :
    List.append (projectionRepeatedCells chunk n) chunk =
      List.append chunk (projectionRepeatedCells chunk n) := by
  rw [← projectionRepeatedCells_succ_right]
  rfl

theorem projectionRepeatedCells_length
    (chunk : List (Option Bool)) (n : Nat) :
    (projectionRepeatedCells chunk n).length = chunk.length * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (List.append chunk (projectionRepeatedCells chunk n)).length =
        chunk.length * (n + 1)
      simp [List.length_append, ih]
      rw [Nat.mul_succ]
      omega

theorem projectionRepeatedCells_reverse
    (chunk : List (Option Bool)) (n : Nat) :
    (projectionRepeatedCells chunk n).reverse =
      projectionRepeatedCells chunk.reverse n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (List.append chunk (projectionRepeatedCells chunk n)).reverse =
          projectionRepeatedCells chunk.reverse (n + 1)
      simp [List.reverse_append, ih, projectionRepeatedCells_succ_right]

def projectionBoolPayloadCells : Word Bool -> List (Option Bool)
  | [] => []
  | b :: rest =>
      List.append (projectionBoolCellCodeCells b)
        (projectionBoolPayloadCells rest)

def projectionMarkedBoolPayloadCells : Word Bool -> List (Option Bool)
  | [] => []
  | b :: rest =>
      List.append (projectionMarkedBoolCellCodeCells b)
        (projectionMarkedBoolPayloadCells rest)

theorem projectionBoolPayloadCells_length
    (w : Word Bool) :
    (projectionBoolPayloadCells w).length = 4 * w.length := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [projectionBoolPayloadCells, projectionBoolCellCodeCells,
          encodeCodeSymbolAsInput, ih] <;>
        omega

theorem projectionMarkedBoolPayloadCells_length
    (w : Word Bool) :
    (projectionMarkedBoolPayloadCells w).length = 4 * w.length := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [projectionMarkedBoolPayloadCells,
          projectionMarkedBoolCellCodeCells, ih] <;>
        omega

@[simp] theorem projectionBoolPayloadCells_append
    (left right : Word Bool) :
    projectionBoolPayloadCells (List.append left right) =
      List.append (projectionBoolPayloadCells left)
        (projectionBoolPayloadCells right) := by
  induction left with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        List.append (projectionBoolCellCodeCells b)
            (projectionBoolPayloadCells (List.append rest right)) =
          List.append
            (List.append (projectionBoolCellCodeCells b)
              (projectionBoolPayloadCells rest))
            (projectionBoolPayloadCells right)
      rw [ih]
      simp [List.append_assoc]

@[simp] theorem projectionMarkedBoolPayloadCells_append
    (left right : Word Bool) :
    projectionMarkedBoolPayloadCells (List.append left right) =
      List.append (projectionMarkedBoolPayloadCells left)
        (projectionMarkedBoolPayloadCells right) := by
  induction left with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells (List.append rest right)) =
          List.append
            (List.append (projectionMarkedBoolCellCodeCells b)
              (projectionMarkedBoolPayloadCells rest))
            (projectionMarkedBoolPayloadCells right)
      rw [ih]
      simp [List.append_assoc]

@[simp] theorem projectionMarkedBoolPayloadCells_append_false
    (marked : Word Bool) :
    projectionMarkedBoolPayloadCells (List.append marked [false]) =
      List.append (projectionMarkedBoolPayloadCells marked)
        (projectionMarkedBoolCellCodeCells false) := by
  simpa [projectionMarkedBoolPayloadCells] using
    projectionMarkedBoolPayloadCells_append marked ([false] : Word Bool)

@[simp] theorem projectionMarkedBoolPayloadCells_append_true
    (marked : Word Bool) :
    projectionMarkedBoolPayloadCells (List.append marked [true]) =
      List.append (projectionMarkedBoolPayloadCells marked)
        (projectionMarkedBoolCellCodeCells true) := by
  simpa [projectionMarkedBoolPayloadCells] using
    projectionMarkedBoolPayloadCells_append marked ([true] : Word Bool)

def projectionBoolWordWorkCells
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

def projectionAllMarkedBoolWordCells (w : Word Bool) :
    List (Option Bool) :=
  List.append
    (projectionRepeatedCells projectionMarkedTickCodeCells w.length)
    (List.append projectionDoneCodeCells
      (projectionMarkedBoolPayloadCells w))

def projectionStageTickCellsRev (stage : Nat) : List (Option Bool) :=
  (projectionCodeCells (List.replicate stage MachineCodeSymbol.tick)).reverse

theorem projectionCodeCells_append
    (pre suffix : Word MachineCodeSymbol) :
    projectionCodeCells (List.append pre suffix) =
      List.append (projectionCodeCells pre) (projectionCodeCells suffix) := by
  unfold projectionCodeCells
  rw [encodeCodeWordAsInput_append]
  simp [List.map_append]

theorem projectionCodeCells_filterMap
    (code : Word MachineCodeSymbol) :
    (projectionCodeCells code).filterMap (fun cell => cell) =
      encodeCodeWordAsInput code := by
  simpa [projectionCodeCells] using
    Tape.filterMap_id_map_some
      (encodeCodeWordAsInput code)

theorem encodeNat_eq_replicate_tick_done
    (n : Nat) :
    encodeNat n =
      List.append (List.replicate n MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [encodeNat, ih, List.replicate_succ]

theorem encodeCodeWordAsInput_encodeNat
    (n : Nat) :
    encodeCodeWordAsInput
        (encodeNat n) =
      List.append
        (encodeCodeWordAsInput
          (List.replicate n MachineCodeSymbol.tick))
        (encodeCodeWordAsInput [MachineCodeSymbol.done]) := by
  rw [encodeNat_eq_replicate_tick_done,
    encodeCodeWordAsInput_append]

theorem projectionDoneCodeCells_filterMap :
    projectionDoneCodeCells.filterMap (fun cell => cell) =
      encodeCodeWordAsInput [MachineCodeSymbol.done] := by
  simpa [projectionDoneCodeCells] using
    projectionCodeCells_filterMap [MachineCodeSymbol.done]

theorem projectionCodeCells_replicate_tick
    (n : Nat) :
    projectionCodeCells (List.replicate n MachineCodeSymbol.tick) =
      projectionRepeatedCells projectionTickCodeCells n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have htail :
          List.map some
              (encodeCodeWordAsInput
                (List.replicate n MachineCodeSymbol.tick)) =
            projectionRepeatedCells
              (List.map some
                (encodeCodeSymbolAsInput
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
        projectionTickCodeCells, encodeCodeWordAsInput,
        htail]

theorem projectionBoolPayloadCells_eq
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
          projectionCodeCells, encodeCodeWordAsInput, ih]

theorem projectionCodeCells_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    projectionCodeCells (encodeNatAppend n suffix) =
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
              (encodeNatAppend n suffix)) =
          List.append
            (List.append projectionTickCodeCells
              (projectionCodeCells
                (List.replicate n MachineCodeSymbol.tick)))
            (List.append projectionDoneCodeCells
              (projectionCodeCells suffix))
      rw [ih]
      simp [List.append_assoc]

theorem projectionBoolPayloadCells_append_eq_encodeCellsAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    List.append (projectionBoolPayloadCells w) (projectionCodeCells suffix) =
      projectionCodeCells
        (encodeCellsAppend (w.map some) suffix) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b
      · simp [projectionBoolPayloadCells, projectionBoolCellCodeCells,
          projectionCodeCells, encodeCellsAppend,
          encodeCellAppend, encodeCell,
          encodeCodeWordAsInput, List.append_assoc]
        simpa [projectionCodeCells] using ih
      · simp [projectionBoolPayloadCells, projectionBoolCellCodeCells,
          projectionCodeCells, encodeCellsAppend,
          encodeCellAppend, encodeCell,
          encodeCodeWordAsInput, List.append_assoc]
        simpa [projectionCodeCells] using ih

theorem projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    projectionBoolWordWorkCells [] w suffix =
      projectionCodeCells (encodeBoolWordAppend w suffix) := by
  simp [projectionBoolWordWorkCells, projectionRepeatedCells,
    projectionMarkedBoolPayloadCells, encodeBoolWordAppend,
    encodeCellListAppend,
    projectionCodeCells_encodeNatAppend]
  exact projectionBoolPayloadCells_append_eq_encodeCellsAppend w suffix

theorem projectionCodeCells_encodeBoolWord
    (w : Word Bool) :
    projectionCodeCells (encodeBoolWord w) =
      List.append
        (projectionRepeatedCells projectionTickCodeCells w.length)
        (List.append projectionDoneCodeCells
          (projectionBoolPayloadCells w)) := by
  have h :=
    projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend w
      ([] : Word MachineCodeSymbol)
  change
    projectionCodeCells (encodeBoolWordAppend w []) =
      List.append
        (projectionRepeatedCells projectionTickCodeCells w.length)
        (List.append projectionDoneCodeCells
          (projectionBoolPayloadCells w))
  rw [← h]
  have hnil :
      projectionCodeCells ([] : Word MachineCodeSymbol) = [] := rfl
  simp [projectionBoolWordWorkCells, projectionRepeatedCells,
    projectionMarkedBoolPayloadCells, projectionCodeCells_replicate_tick,
    hnil]

def Description :
    MachineDescription where
  stateCount := 1000
  start := 0
  halt := 999
  transitions :=
    [ erase 0 (some false) 1
    , erase 1 (some false) 2
    , erase 2 (some false) 3
    , erase 3 (some false) 100

    -- Validate the input bool-word length prefix, marking ticks and cells.
    , keep 100 false 101
    , keep 101 false 102
    , keep 102 true 103
    , writeMove 103 (some false) none Direction.right 120
    , keep 103 true 150
    , keepMove 103 none Direction.right 100

    -- Skip the remaining input length prefix to find the matching cell.
    , keep 120 false 121
    , keep 121 false 122
    , keep 122 true 123
    , keep 123 false 120
    , keep 123 true 130
    , keepMove 123 none Direction.right 120

    -- Mark one unprocessed input cell for the tick just marked.
    , keep 130 false 131
    , writeMove 131 (some true) none Direction.right 132
    , keepMove 131 none Direction.right 135
    , keep 132 false 133
    , keep 132 true 134
    , keepMove 133 (some true) Direction.left 140
    , keepMove 134 (some false) Direction.left 140
    , keep 135 false 136
    , keep 135 true 137
    , keep 136 true 130
    , keep 137 false 130

    -- No unmarked ticks remain: ensure all input cells were processed.
    , keep 150 false 151
    , keepMove 151 none Direction.right 152
    , keepMove 151 (some false) Direction.left 160
    , keep 152 false 153
    , keep 152 true 154
    , keep 153 true 150
    , keep 154 false 150

    -- Restore the marked input prefix, then continue at the stage nat.
    , keepMove 164 none Direction.right 165
    , keepMove 165 none Direction.right 166
    , keepMove 166 none Direction.right 170
    , keep 170 false 171
    , keep 171 false 172
    , keep 172 true 173
    , keep 173 false 170
    , writeMove 173 none (some false) Direction.right 170
    , keep 173 true 180
    , keep 180 false 181
    , writeMove 181 none (some true) Direction.right 182
    , keepMove 181 (some false) Direction.left 200
    , keep 182 false 183
    , keep 182 true 184
    , keep 183 true 180
    , keep 184 false 180

    -- Preserve and validate the stage nat prefix.
    , keep 200 false 201
    , keep 201 false 202
    , keep 202 true 203
    , keep 203 false 200
    , keep 203 true 210

    -- Mark the stage-nat terminator as a four-blank boundary.
    , keepMove 210 (some false) Direction.left 211
    , writeMove 211 (some true) none Direction.left 212
    , writeMove 212 (some true) none Direction.left 213
    , writeMove 213 (some false) none Direction.left 214
    , writeMove 214 (some false) none Direction.right 215
    , keepMove 215 none Direction.right 216
    , keepMove 216 none Direction.right 217
    , keepMove 217 none Direction.right 300

    -- Validate the result bool-word length prefix, marking ticks and cells.
    , keep 300 false 301
    , keep 301 false 302
    , keep 302 true 303
    , writeMove 303 (some false) none Direction.right 320
    , keep 303 true 350
    , keepMove 303 none Direction.right 300

    -- Skip the remaining result length prefix to find the matching cell.
    , keep 320 false 321
    , keep 321 false 322
    , keep 322 true 323
    , keep 323 false 320
    , keep 323 true 330
    , keepMove 323 none Direction.right 320

    -- Mark one unprocessed result cell for the tick just marked.
    , keep 330 false 331
    , writeMove 331 (some true) none Direction.right 332
    , keepMove 331 none Direction.right 335
    , keep 332 false 333
    , keep 332 true 334
    , keepMove 333 (some true) Direction.left 340
    , keepMove 334 (some false) Direction.left 340
    , keep 335 false 336
    , keep 335 true 337
    , keep 336 true 330
    , keep 337 false 330

    -- No unmarked ticks remain: ensure all result cells were processed.
    , keep 350 false 351
    , keepMove 350 none Direction.left 360
    , keepMove 351 none Direction.right 352
    , keep 352 false 353
    , keep 352 true 354
    , keep 353 true 350
    , keep 354 false 350

    -- Restore the stage-nat terminator boundary.
    , writeMove 363 none (some false) Direction.right 364
    , writeMove 364 none (some false) Direction.right 365
    , writeMove 365 none (some true) Direction.right 366
    , writeMove 366 none (some true) Direction.right 367

    -- Blank the validated result length prefix and cell payload.
    , erase 367 (some false) 368
    , erase 368 (some false) 369
    , erase 369 (some true) 370
    , erase 370 (some false) 367
    , erase 370 none 367
    , erase 370 (some true) 380
    , erase 380 (some false) 381
    , erase 380 none 999
    , erase 381 none 382
    , erase 382 (some false) 383
    , erase 382 (some true) 384
    , erase 383 (some true) 380
    , erase 384 (some false) 380 ]
      ++ scanLeftToBoundary 140 141 142 143 144
      ++
    [ keepMove 144 none Direction.right 145
    , keepMove 145 none Direction.right 146
    , keepMove 146 none Direction.right 100 ]
      ++ scanLeftToBoundary 160 161 162 163 164
      ++ scanLeftToBoundary 340 341 342 343 344
      ++
    [ keepMove 344 none Direction.right 345
    , keepMove 345 none Direction.right 346
    , keepMove 346 none Direction.right 300 ]
      ++
    [ keepMove 360 none Direction.left 361
    , keepMove 360 (some false) Direction.left 360
    , keepMove 360 (some true) Direction.left 360
    , keepMove 361 none Direction.left 362
    , keepMove 361 (some false) Direction.left 360
    , keepMove 361 (some true) Direction.left 360
    , keepMove 362 none Direction.left 363
    , keepMove 362 (some false) Direction.left 360
    , keepMove 362 (some true) Direction.left 360
    , keepMove 363 (some false) Direction.left 360
    , keepMove 363 (some true) Direction.left 360 ]

theorem wellFormed :
    Description.WellFormed := by
  refine ⟨by simp [Description], by simp [Description],
    by simp [Description], ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := Description.transitions)
      (stateCount := Description.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := Description.transitions)
      (by native_decide)

theorem haltTransitionFree :
    Description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := Description.transitions)
    (state := Description.halt)
    (by native_decide)

theorem run_header
    (suffix : Word Bool) :
    Description.runConfig 4
        (Description.initial
          (List.append [false, false, false, false] suffix)) =
      { state := 100
        tape := projectionTapeAt [none, none, none, none] suffix } := by
  cases suffix with
  | nil =>
      rfl
  | cons b _ =>
      cases b <;> rfl

theorem run_stage_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
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

theorem run_stage_done
    (leftRev rest : List (Option Bool)) :
    Description.runConfig 12
        (projectionConfig 200 leftRev
          (List.append projectionDoneCodeCells (some false :: rest))) =
      projectionConfig 300
        (List.append [none, none, none, none] leftRev)
        (some false :: rest) := by
  rfl

theorem projectionStageTickCellsRev_succ
    (stage : Nat) :
    projectionStageTickCellsRev (stage + 1) =
      List.append (projectionStageTickCellsRev stage)
        projectionTickCodeCellsRev := by
  unfold projectionStageTickCellsRev projectionTickCodeCellsRev
  rw [projectionCodeCells_replicate_tick]
  rw [projectionCodeCells_replicate_tick]
  rw [show projectionRepeatedCells projectionTickCodeCells (stage + 1) =
      List.append projectionTickCodeCells
        (projectionRepeatedCells projectionTickCodeCells stage) by
    rfl]
  simp [List.reverse_append]

theorem run_stage_nat
    (stage : Nat) (leftRev : List (Option Bool)) (result : Word Bool) :
    Description.runConfig
        (4 * stage + 12)
        (projectionConfig 200 leftRev
          (projectionCodeCells
            (encodeNatAppend stage
              (encodeBoolWord result)))) =
      projectionConfig 300
        (List.append [none, none, none, none]
          (List.append (projectionStageTickCellsRev stage) leftRev))
        (projectionCodeCells (encodeBoolWord result)) := by
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
      rw [hsteps, runConfig_add]
      change Description.runConfig
          (4 * stage + 12)
          (Description.runConfig 4
            (projectionConfig 200 leftRev
              (projectionCodeCells
                (encodeNatAppend (stage + 1)
                  (encodeBoolWord result))))) = _
      have hsucc : stage + 1 = Nat.succ stage := by omega
      have hcells :
          projectionCodeCells
              (encodeNatAppend (stage + 1)
                (encodeBoolWord result)) =
            List.append projectionTickCodeCells
              (projectionCodeCells
                (encodeNatAppend stage
                  (encodeBoolWord result))) := by
        rw [hsucc]
        rfl
      rw [hcells]
      rw [run_stage_tick]
      rw [ih]
      rw [projectionStageTickCellsRev_succ]
      simp [projectionConfig, projectionTapeAtCells, List.append_assoc]

theorem run_stage_nat_bool_word_suffix
    (stage : Nat) (leftRev : List (Option Bool)) (result : Word Bool)
    (suffix : Word MachineCodeSymbol) :
    Description.runConfig
        (4 * stage + 12)
        (projectionConfig 200 leftRev
          (projectionCodeCells
            (encodeNatAppend stage
              (encodeBoolWordAppend result suffix)))) =
      projectionConfig 300
        (List.append [none, none, none, none]
          (List.append (projectionStageTickCellsRev stage) leftRev))
        (projectionCodeCells
          (encodeBoolWordAppend result suffix)) := by
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
      rw [hsteps, runConfig_add]
      change Description.runConfig
          (4 * stage + 12)
          (Description.runConfig 4
            (projectionConfig 200 leftRev
              (projectionCodeCells
                (encodeNatAppend (stage + 1)
                  (encodeBoolWordAppend result suffix))))) =
        _
      have hsucc : stage + 1 = Nat.succ stage := by omega
      have hcells :
          projectionCodeCells
              (encodeNatAppend (stage + 1)
                (encodeBoolWordAppend result suffix)) =
            List.append projectionTickCodeCells
              (projectionCodeCells
                (encodeNatAppend stage
                  (encodeBoolWordAppend result suffix))) := by
        rw [hsucc]
        rfl
      rw [hcells]
      rw [run_stage_tick]
      rw [ih]
      rw [projectionStageTickCellsRev_succ]
      simp [projectionConfig, projectionTapeAtCells, List.append_assoc]

theorem run_cleanup_marked_tick
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
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

theorem run_cleanup_marked_ticks
    (count : Nat) (leftRev tail : List (Option Bool)) :
    Description.runConfig (4 * count)
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
      rw [hsteps, runConfig_add]
      change Description.runConfig
          (4 * count)
          (Description.runConfig 4
            (projectionConfig 367 leftRev
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  (count + 1)) tail))) = _
      rw [show projectionRepeatedCells projectionMarkedTickCodeCells
          (count + 1) =
          List.append projectionMarkedTickCodeCells
            (projectionRepeatedCells projectionMarkedTickCodeCells count) by
        rfl]
      change Description.runConfig
          (4 * count)
          (Description.runConfig 4
            (projectionConfig 367 leftRev
              (List.append projectionMarkedTickCodeCells
                (List.append
                  (projectionRepeatedCells projectionMarkedTickCodeCells count)
                  tail)))) = _
      rw [run_cleanup_marked_tick]
      rw [ih]
      rw [show 4 + 4 * count = 4 * count + 4 by omega]
      have hrep :
          List.replicate (4 * count + 4) (none : Option Bool) =
            List.append (List.replicate (4 * count) (none : Option Bool))
              ([none, none, none, none] : List (Option Bool)) := by
        simp [List.replicate_succ', List.append_assoc]
      rw [hrep]
      simp [List.append_assoc]

theorem run_cleanup_done
    (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
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

theorem run_cleanup_marked_payload_cell
    (b : Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig 4
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

theorem run_cleanup_marked_payload
    (w : Word Bool) (leftRev : List (Option Bool)) :
    Description.runConfig
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
      rw [hsteps, runConfig_add]
      change Description.runConfig
          (4 * rest.length + 1)
          (Description.runConfig 4
            (projectionConfig 380 leftRev
              (projectionMarkedBoolPayloadCells (b :: rest)))) = _
      rw [show projectionMarkedBoolPayloadCells (b :: rest) =
          List.append (projectionMarkedBoolCellCodeCells b)
            (projectionMarkedBoolPayloadCells rest) by
        rfl]
      rw [run_cleanup_marked_payload_cell]
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

theorem run_cleanup_marked_payload_to_tail
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig
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
      rw [hsteps, runConfig_add]
      change Description.runConfig
          (4 * rest.length)
          (Description.runConfig 4
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
      rw [run_cleanup_marked_payload_cell
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

theorem run_cleanup_all_marked_to_tail
    (w : Word Bool) (leftRev tail : List (Option Bool)) :
    Description.runConfig
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
  rw [hsteps, runConfig_add]
  change Description.runConfig
      (4 + 4 * w.length)
      (Description.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (List.append (projectionAllMarkedBoolWordCells w) tail))) = _
  simp [projectionAllMarkedBoolWordCells, List.append_assoc]
  change Description.runConfig
      (4 + 4 * w.length)
      (Description.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells w.length)
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells w) tail))))) = _
  have hticks :=
    run_cleanup_marked_ticks
      (count := w.length) (leftRev := leftRev)
      (tail := List.append projectionDoneCodeCells
        (List.append (projectionMarkedBoolPayloadCells w) tail))
  rw [hticks]
  rw [show 4 + 4 * w.length = 4 + 4 * w.length by rfl,
    runConfig_add]
  change Description.runConfig
      (4 * w.length)
      (Description.runConfig 4
        (projectionConfig 367
          (List.append (List.replicate (4 * w.length) none) leftRev)
          (List.append projectionDoneCodeCells
            (List.append (projectionMarkedBoolPayloadCells w) tail)))) = _
  rw [run_cleanup_done]
  rw [run_cleanup_marked_payload_to_tail]
  simp

theorem state_ne_halt_of_stepConfig_none
    {c : Configuration} {n : Nat}
    (hstep :
      Description.stepConfig c = none)
    (hstate : c.state ≠ Description.halt) :
    (Description.runConfig n c).state ≠
      Description.halt := by
  have hrun :=
    runConfig_of_stepConfig_none
      (D := Description)
      hstep n
  rw [hrun]
  exact hstate

theorem run_state380_true_ne_halt
    (leftRev tail : List (Option Bool)) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 380 leftRev (some true :: tail))).state ≠
      Description.halt := by
  apply
    state_ne_halt_of_stepConfig_none
  · rfl
  · simp [projectionConfig, Description]

theorem run_state381_nonblank_ne_halt
    (b : Bool) (leftRev tail : List (Option Bool)) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 381 leftRev (some b :: tail))).state ≠
      Description.halt := by
  apply
    state_ne_halt_of_stepConfig_none
  · cases b <;> rfl
  · simp [projectionConfig, Description]

theorem run_state380_false_nonblank_next_ne_halt
    (b : Bool) (leftRev tail : List (Option Bool)) (n : Nat) :
    (Description.runConfig (n + 1)
      (projectionConfig 380 leftRev (some false :: some b :: tail))).state ≠
      Description.halt := by
  change
    (Description.runConfig n
      (projectionConfig 381 (none :: leftRev) (some b :: tail))).state ≠
      Description.halt
  exact
    run_state381_nonblank_ne_halt
      b (none :: leftRev) tail n

theorem run_cleanup_code_suffix_ne_halt
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 380 leftRev
        (projectionCodeCells (symbol :: suffix)))).state ≠
      Description.halt := by
  cases n with
  | zero =>
      change (380 : Nat) ≠ 999
      omega
  | succ n =>
      cases symbol <;>
        simp [projectionCodeCells, encodeCodeWordAsInput,
          encodeCodeSymbolAsInput]
      · exact
          run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some false :: some false ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some false :: some true ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some true :: some false ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            false leftRev
            (some true :: some true ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some false :: some false ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some false :: some true ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some true :: some false ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_false_nonblank_next_ne_halt
            true leftRev
            (some true :: some true ::
              List.map some (encodeCodeWordAsInput suffix))
            n
      · exact
          run_state380_true_ne_halt
            leftRev
            (some false :: some false :: some false ::
              List.map some (encodeCodeWordAsInput suffix))
            (n + 1)

theorem run_cleanup_all_marked_code_suffix_after_prefix_ne_halt
    (w : Word Bool) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (n : Nat) :
    (Description.runConfig
      (8 * w.length + 4 + n)
      (projectionConfig 367 leftRev
        (List.append (projectionAllMarkedBoolWordCells w)
          (projectionCodeCells (symbol :: suffix))))).state ≠
      Description.halt := by
  rw [show 8 * w.length + 4 + n = (8 * w.length + 4) + n by omega,
    runConfig_add]
  rw [run_cleanup_all_marked_to_tail]
  exact
    run_cleanup_code_suffix_ne_halt
      symbol suffix
      (List.append (List.replicate (4 * w.length) none)
        (List.append [none, none, none, none]
          (List.append (List.replicate (4 * w.length) none) leftRev)))
      n

theorem run_cleanup_all_marked
    (w : Word Bool) (leftRev : List (Option Bool)) :
    Description.runConfig
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
  rw [hsteps, runConfig_add]
  change Description.runConfig
      (4 + (4 * w.length + 1))
      (Description.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (projectionAllMarkedBoolWordCells w))) = _
  simp [projectionAllMarkedBoolWordCells]
  change Description.runConfig
      (4 + (4 * w.length + 1))
      (Description.runConfig
        (4 * w.length)
        (projectionConfig 367 leftRev
          (List.append
            (projectionRepeatedCells projectionMarkedTickCodeCells w.length)
            (List.append projectionDoneCodeCells
              (projectionMarkedBoolPayloadCells w))))) = _
  rw [run_cleanup_marked_ticks
    (count := w.length) (leftRev := leftRev)
    (tail := List.append projectionDoneCodeCells
      (projectionMarkedBoolPayloadCells w))]
  rw [show 4 + (4 * w.length + 1) = 4 + (4 * w.length + 1) by rfl,
    runConfig_add]
  change Description.runConfig
      (4 * w.length + 1)
      (Description.runConfig 4
        (projectionConfig 367
          (List.append (List.replicate (4 * w.length) none) leftRev)
          (List.append projectionDoneCodeCells
            (projectionMarkedBoolPayloadCells w)))) = _
  rw [run_cleanup_done]
  rw [run_cleanup_marked_payload]
  simp

theorem run_cleanup_all_marked_code_suffix_fixed_halt_iff
    (w : Word Bool) (suffix : Word MachineCodeSymbol)
    (leftRev : List (Option Bool)) :
    (Description.runConfig
      (8 * w.length + 5)
      (projectionConfig 367 leftRev
        (List.append (projectionAllMarkedBoolWordCells w)
          (projectionCodeCells suffix)))).state =
        Description.halt <->
      suffix = [] := by
  constructor
  · intro h
    cases suffix with
    | nil =>
        rfl
    | cons symbol rest =>
        exact False.elim
          (run_cleanup_all_marked_code_suffix_after_prefix_ne_halt
            w symbol rest leftRev 1 h)
  · intro h
    subst suffix
    simp [projectionCodeCells, encodeCodeWordAsInput]
    rw [run_cleanup_all_marked]
    rfl

end ControllerStageInputProjection
end Computability
end FoC

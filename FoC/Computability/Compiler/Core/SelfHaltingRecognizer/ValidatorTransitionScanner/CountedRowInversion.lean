import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsFailures
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsLoopRuns

set_option doc.verso true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# Exact-code validator: one-row inversion

Canonical transition-code tokens are classified constructively. A complete bounded row
produces its decoded transition and exact logical return run; every other shape
produces a compiler-level stuck witness.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorCountedRows

open Languages
open MachineDescription

private def transitionBodyAppend
    (row : TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend row.source
    (encodeCellAppend row.read
      (encodeCellAppend row.write
        (encodeDirectionAppend row.move
          (encodeNatAppend row.target suffix))))

private theorem canonicalBlocks_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeCellAppend cell suffix) =
      cellBlock cell :: validatorCanonicalBlocks suffix := by
  cases cell with
  | none => rfl
  | some bit => cases bit <;> rfl

private theorem canonicalBlocks_encodeDirectionAppend
    (move : Direction) (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeDirectionAppend move suffix) =
      directionBlock move :: validatorCanonicalBlocks suffix := by
  cases move <;> rfl

private inductive NatTokenView :
    Word MachineCodeSymbol -> Type where
  | parsed (value : Nat) (rest : Word MachineCodeSymbol)
      (tokens_eq : tokens = encodeNatAppend value rest) : NatTokenView tokens
  | malformed (ticks : Nat) (bad : MachineCodeSymbol)
      (rest : Word MachineCodeSymbol)
      (tokens_eq : tokens =
        List.append (List.replicate ticks .tick) (bad :: rest))
      (bad_ne_tick : bad ≠ .tick) (bad_ne_done : bad ≠ .done) :
      NatTokenView tokens
  | unterminated (ticks : Nat)
      (tokens_eq : tokens = List.replicate ticks .tick) :
      NatTokenView tokens

private def natTokenView :
    (tokens : Word MachineCodeSymbol) -> NatTokenView tokens
  | [] => .unterminated 0 rfl
  | .done :: rest => .parsed 0 rest rfl
  | .tick :: rest =>
      match natTokenView rest with
      | .parsed value suffix heq =>
          .parsed (value + 1) suffix (by
            simp [encodeNatAppend, encodeNat, heq])
      | .malformed ticks bad suffix heq htick hdone =>
          .malformed (ticks + 1) bad suffix (by
            simp [heq, List.replicate_succ])
            htick hdone
      | .unterminated ticks heq =>
          .unterminated (ticks + 1) (by
            simp [heq, List.replicate_succ])
  | .header :: rest => .malformed 0 .header rest rfl (by decide) (by decide)
  | .transition :: rest =>
      .malformed 0 .transition rest rfl (by decide) (by decide)
  | .blank :: rest => .malformed 0 .blank rest rfl (by decide) (by decide)
  | .zero :: rest => .malformed 0 .zero rest rfl (by decide) (by decide)
  | .one :: rest => .malformed 0 .one rest rfl (by decide) (by decide)
  | .moveLeft :: rest =>
      .malformed 0 .moveLeft rest rfl (by decide) (by decide)
  | .moveRight :: rest =>
      .malformed 0 .moveRight rest rfl (by decide) (by decide)

private inductive CellTokenView :
    Word MachineCodeSymbol -> Type where
  | parsed (cell : Option Bool) (rest : Word MachineCodeSymbol)
      (tokens_eq : tokens = encodeCellAppend cell rest) :
      CellTokenView tokens
  | missing : CellTokenView []
  | malformed (bad : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
      (tokens_eq : tokens = bad :: rest)
      (bad_ne_blank : bad ≠ .blank)
      (bad_ne_zero : bad ≠ .zero)
      (bad_ne_one : bad ≠ .one) : CellTokenView tokens

private def cellTokenView :
    (tokens : Word MachineCodeSymbol) -> CellTokenView tokens
  | [] => .missing
  | .blank :: rest => .parsed none rest rfl
  | .zero :: rest => .parsed (some false) rest rfl
  | .one :: rest => .parsed (some true) rest rfl
  | .header :: rest =>
      .malformed .header rest rfl (by decide) (by decide) (by decide)
  | .transition :: rest =>
      .malformed .transition rest rfl (by decide) (by decide) (by decide)
  | .tick :: rest =>
      .malformed .tick rest rfl (by decide) (by decide) (by decide)
  | .done :: rest =>
      .malformed .done rest rfl (by decide) (by decide) (by decide)
  | .moveLeft :: rest =>
      .malformed .moveLeft rest rfl (by decide) (by decide) (by decide)
  | .moveRight :: rest =>
      .malformed .moveRight rest rfl (by decide) (by decide) (by decide)

private inductive DirectionTokenView :
    Word MachineCodeSymbol -> Type where
  | parsed (move : Direction) (rest : Word MachineCodeSymbol)
      (tokens_eq : tokens = encodeDirectionAppend move rest) :
      DirectionTokenView tokens
  | missing : DirectionTokenView []
  | malformed (bad : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
      (tokens_eq : tokens = bad :: rest)
      (bad_ne_left : bad ≠ .moveLeft)
      (bad_ne_right : bad ≠ .moveRight) : DirectionTokenView tokens

private def directionTokenView :
    (tokens : Word MachineCodeSymbol) -> DirectionTokenView tokens
  | [] => .missing
  | .moveLeft :: rest => .parsed Direction.left rest rfl
  | .moveRight :: rest => .parsed Direction.right rest rfl
  | .header :: rest => .malformed .header rest rfl (by decide) (by decide)
  | .transition :: rest =>
      .malformed .transition rest rfl (by decide) (by decide)
  | .tick :: rest => .malformed .tick rest rfl (by decide) (by decide)
  | .done :: rest => .malformed .done rest rfl (by decide) (by decide)
  | .blank :: rest => .malformed .blank rest rfl (by decide) (by decide)
  | .zero :: rest => .malformed .zero rest rfl (by decide) (by decide)
  | .one :: rest => .malformed .one rest rfl (by decide) (by decide)

private def canonicalLeafWitness
    (logical : Nat) (left : Word ValidatorBlockSymbol)
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (hlogical : logical < blockDescription.stateCount)
    (hnotHalt : logical ≠ blockDescription.halt)
    (hleafNone :
      Description.lookupTransition
          (validatorBlockLeafState logical
            (ValidatorBlockSymbol.ofMachineCodeSymbol symbol))
          (some
            (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).fourthBit) =
        none)
    (hleafNotHalt :
      validatorBlockLeafState logical
          (ValidatorBlockSymbol.ofMachineCodeSymbol symbol) ≠
        Description.halt) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration logical left
        (validatorCanonicalBlocks (symbol :: rest))) :=
  .leaf
    { logical := logical
      left := left
      right := validatorCanonicalBlocks rest
      read := ValidatorBlockSymbol.ofMachineCodeSymbol symbol
      reaches := by
        simpa [configuration, validatorCanonicalBlocks] using
          ValidatorBlockDescription.reaches_refl blockDescription
            (configuration logical left
              (validatorCanonicalBlocks (symbol :: rest)))
      logical_lt := hlogical
      logical_ne_halt := hnotHalt
      leaf_none := hleafNone
      leaf_ne_halt := hleafNotHalt }

private def canonicalBlankWitness
    (logical : Nat) (left : Word ValidatorBlockSymbol)
    (hlogical : logical < blockDescription.stateCount)
    (hnotHalt : logical ≠ blockDescription.halt)
    (hrootNone :
      Description.lookupTransition
        (validatorBlockRootState logical) none = none)
    (hrootNotHalt : validatorBlockRootState logical ≠ Description.halt) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration logical left (validatorCanonicalBlocks [])) :=
  .rootBlank
    { logical := logical
      left := left
      reaches := by
        simpa [configuration, validatorCanonicalBlocks] using
          ValidatorBlockDescription.reaches_refl blockDescription
            (configuration logical left [])
      logical_lt := hlogical
      logical_ne_halt := hnotHalt
      root_none := hrootNone
      root_ne_halt := hrootNotHalt }

private structure CheckedRowSuccess
    (stateCount : Nat) (middle : Word ValidatorBlockSymbol)
    (tokens : Word MachineCodeSymbol) where
  row : TransitionDescription
  rest : Word MachineCodeSymbol
  tokens_eq : tokens = transitionBodyAppend row rest
  source_lt : row.source < stateCount
  target_lt : row.target < stateCount
  reaches : blockDescription.Reaches
    (configuration 8 (sourcePairLeft stateCount 0 middle)
      (validatorCanonicalBlocks tokens))
    (configuration 0
      (restoredRowLeft stateCount row.target row middle)
      (.done :: validatorCanonicalBlocks rest))

private inductive CheckedRowOutcome
    (stateCount : Nat) (middle : Word ValidatorBlockSymbol)
    (tokens : Word MachineCodeSymbol) where
  | success : CheckedRowSuccess stateCount middle tokens ->
      CheckedRowOutcome stateCount middle tokens
  | stuck : ValidatorBlockStuckWitness blockDescription Description
      (configuration 8 (sourcePairLeft stateCount 0 middle)
        (validatorCanonicalBlocks tokens)) ->
      CheckedRowOutcome stateCount middle tokens

private def sourceMalformedStuckWitness
    (stateCount ticks : Nat) (bad : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hbadTick : bad ≠ .tick) (hbadDone : bad ≠ .done) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 8 (sourcePairLeft stateCount 0 middle)
        (validatorCanonicalBlocks
          (List.append (List.replicate ticks .tick) (bad :: rest)))) := by
  by_cases hle : ticks ≤ stateCount
  · let stateRemaining := stateCount - ticks
    have hdecomp : stateCount = stateRemaining + ticks := by
      dsimp [stateRemaining]
      lia
    have hpairs := reaches_pair_all_source_ticks
      stateRemaining ticks 0 middle
      (validatorCanonicalBlocks (bad :: rest)) hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 8 (sourcePairLeft stateCount 0 middle)
            (validatorCanonicalBlocks
              (List.append (List.replicate ticks .tick) (bad :: rest))))
          (configuration 8 (sourcePairLeft stateRemaining ticks middle)
            (validatorCanonicalBlocks (bad :: rest))) := by
      simpa [hdecomp, validatorCanonicalBlocks_append,
        validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol] using hpairs
    cases bad with
    | tick => contradiction
    | done => contradiction
    | header =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .header rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | transition =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .transition rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | blank =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .blank rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | zero =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .zero rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | one =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .one rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | moveLeft =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .moveLeft rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | moveRight =>
        exact (canonicalLeafWitness 8
          (sourcePairLeft stateRemaining ticks middle)
          .moveRight rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
  · let extra := ticks - (stateCount + 1)
    have hdecomp : ticks = stateCount + (extra + 1) := by
      dsimp [extra]
      lia
    let remainingTokens : Word MachineCodeSymbol :=
      List.append (List.replicate extra .tick) (bad :: rest)
    let remainingBlocks : Word ValidatorBlockSymbol :=
      validatorCanonicalBlocks remainingTokens
    have hpairs := reaches_pair_all_source_ticks
      0 stateCount 0 middle
      (validatorCanonicalBlocks
        (List.append (List.replicate (extra + 1) .tick) (bad :: rest)))
      hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 8 (sourcePairLeft stateCount 0 middle)
            (validatorCanonicalBlocks
              (List.append (List.replicate ticks .tick) (bad :: rest))))
          (configuration 8 (sourcePairLeft 0 stateCount middle)
            (.tick :: remainingBlocks)) := by
      simpa [hdecomp, remainingBlocks, remainingTokens,
        validatorCanonicalBlocks_append, validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol,
        List.replicate_succ, list_replicate_add_append,
        List.append_assoc] using hpairs
    exact (sourceExtraTickStuckWitness
      stateCount middle remainingBlocks hmiddle).prepend hpairs'

private def sourceUnterminatedStuckWitness
    (stateCount ticks : Nat) (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 8 (sourcePairLeft stateCount 0 middle)
        (validatorCanonicalBlocks (List.replicate ticks .tick))) := by
  by_cases hle : ticks ≤ stateCount
  · let stateRemaining := stateCount - ticks
    have hdecomp : stateCount = stateRemaining + ticks := by
      dsimp [stateRemaining]
      lia
    have hpairs := reaches_pair_all_source_ticks
      stateRemaining ticks 0 middle [] hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 8 (sourcePairLeft stateCount 0 middle)
            (validatorCanonicalBlocks (List.replicate ticks .tick)))
          (configuration 8 (sourcePairLeft stateRemaining ticks middle) []) := by
      simpa [hdecomp, validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol] using hpairs
    exact (canonicalBlankWitness 8
      (sourcePairLeft stateRemaining ticks middle)
      (by decide) (by decide) (by decide) (by decide)).prepend hpairs'
  · let extra := ticks - (stateCount + 1)
    have hdecomp : ticks = stateCount + (extra + 1) := by
      dsimp [extra]
      lia
    let remainingBlocks : Word ValidatorBlockSymbol :=
      validatorCanonicalBlocks (List.replicate extra .tick)
    have hpairs := reaches_pair_all_source_ticks
      0 stateCount 0 middle
      (validatorCanonicalBlocks (List.replicate (extra + 1) .tick))
      hmiddle
    have hticks :
        List.replicate ticks MachineCodeSymbol.tick =
          List.append (List.replicate stateCount .tick)
            (.tick :: List.replicate extra .tick) := by
      rw [hdecomp]
      simpa [List.replicate_succ] using
        (list_replicate_add_append MachineCodeSymbol.tick
          stateCount (extra + 1) [])
    have hpairs' :
        blockDescription.Reaches
          (configuration 8 (sourcePairLeft stateCount 0 middle)
            (validatorCanonicalBlocks (List.replicate ticks .tick)))
          (configuration 8 (sourcePairLeft 0 stateCount middle)
            (.tick :: remainingBlocks)) := by
      simpa [hticks, remainingBlocks, validatorCanonicalBlocks_append,
        validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol,
        List.replicate_succ, List.append_assoc] using hpairs
    exact (sourceExtraTickStuckWitness
      stateCount middle remainingBlocks hmiddle).prepend hpairs'

private def targetMalformedStuckWitness
    (stateCount ticks : Nat) (bad : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols)
    (hbadTick : bad ≠ .tick) (hbadDone : bad ≠ .done) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 20 (targetPairLeft stateCount 0 row middle)
        (validatorCanonicalBlocks
          (List.append (List.replicate ticks .tick) (bad :: rest)))) := by
  by_cases hle : ticks ≤ stateCount
  · let stateRemaining := stateCount - ticks
    have hdecomp : stateCount = stateRemaining + ticks := by
      dsimp [stateRemaining]
      lia
    have hpairs := reaches_pair_all_target_ticks
      stateRemaining ticks 0 row middle
      (validatorCanonicalBlocks (bad :: rest)) hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 20 (targetPairLeft stateCount 0 row middle)
            (validatorCanonicalBlocks
              (List.append (List.replicate ticks .tick) (bad :: rest))))
          (configuration 20
            (targetPairLeft stateRemaining ticks row middle)
            (validatorCanonicalBlocks (bad :: rest))) := by
      simpa [hdecomp, validatorCanonicalBlocks_append,
        validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol] using hpairs
    cases bad with
    | tick => contradiction
    | done => contradiction
    | header =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .header rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | transition =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .transition rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | blank =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .blank rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | zero =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .zero rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | one =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .one rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | moveLeft =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .moveLeft rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
    | moveRight =>
        exact (canonicalLeafWitness 20
          (targetPairLeft stateRemaining ticks row middle)
          .moveRight rest (by decide) (by decide) (by decide) (by decide)).prepend
            hpairs'
  · let extra := ticks - (stateCount + 1)
    have hdecomp : ticks = stateCount + (extra + 1) := by
      dsimp [extra]
      lia
    let remainingTokens : Word MachineCodeSymbol :=
      List.append (List.replicate extra .tick) (bad :: rest)
    let remainingBlocks : Word ValidatorBlockSymbol :=
      validatorCanonicalBlocks remainingTokens
    have hpairs := reaches_pair_all_target_ticks
      0 stateCount 0 row middle
      (validatorCanonicalBlocks
        (List.append (List.replicate (extra + 1) .tick) (bad :: rest)))
      hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 20 (targetPairLeft stateCount 0 row middle)
            (validatorCanonicalBlocks
              (List.append (List.replicate ticks .tick) (bad :: rest))))
          (configuration 20 (targetPairLeft 0 stateCount row middle)
            (.tick :: remainingBlocks)) := by
      simpa [hdecomp, remainingBlocks, remainingTokens,
        validatorCanonicalBlocks_append, validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol,
        List.replicate_succ, list_replicate_add_append,
        List.append_assoc] using hpairs
    exact (targetExtraTickStuckWitness
      stateCount row middle remainingBlocks hmiddle).prepend hpairs'

private def targetUnterminatedStuckWitness
    (stateCount ticks : Nat) (row : TransitionDescription)
    (middle : Word ValidatorBlockSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 20 (targetPairLeft stateCount 0 row middle)
        (validatorCanonicalBlocks (List.replicate ticks .tick))) := by
  by_cases hle : ticks ≤ stateCount
  · let stateRemaining := stateCount - ticks
    have hdecomp : stateCount = stateRemaining + ticks := by
      dsimp [stateRemaining]
      lia
    have hpairs := reaches_pair_all_target_ticks
      stateRemaining ticks 0 row middle [] hmiddle
    have hpairs' :
        blockDescription.Reaches
          (configuration 20 (targetPairLeft stateCount 0 row middle)
            (validatorCanonicalBlocks (List.replicate ticks .tick)))
          (configuration 20
            (targetPairLeft stateRemaining ticks row middle) []) := by
      simpa [hdecomp, validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol] using hpairs
    exact (canonicalBlankWitness 20
      (targetPairLeft stateRemaining ticks row middle)
      (by decide) (by decide) (by decide) (by decide)).prepend hpairs'
  · let extra := ticks - (stateCount + 1)
    have hdecomp : ticks = stateCount + (extra + 1) := by
      dsimp [extra]
      lia
    let remainingBlocks : Word ValidatorBlockSymbol :=
      validatorCanonicalBlocks (List.replicate extra .tick)
    have hpairs := reaches_pair_all_target_ticks
      0 stateCount 0 row middle
      (validatorCanonicalBlocks (List.replicate (extra + 1) .tick))
      hmiddle
    have hticks :
        List.replicate ticks MachineCodeSymbol.tick =
          List.append (List.replicate stateCount .tick)
            (.tick :: List.replicate extra .tick) := by
      rw [hdecomp]
      simpa [List.replicate_succ] using
        (list_replicate_add_append MachineCodeSymbol.tick
          stateCount (extra + 1) [])
    have hpairs' :
        blockDescription.Reaches
          (configuration 20 (targetPairLeft stateCount 0 row middle)
            (validatorCanonicalBlocks (List.replicate ticks .tick)))
          (configuration 20 (targetPairLeft 0 stateCount row middle)
            (.tick :: remainingBlocks)) := by
      simpa [hticks, remainingBlocks, validatorCanonicalBlocks_append,
        validatorCanonicalBlocks,
        ValidatorBlockSymbol.ofMachineCodeSymbol,
        List.replicate_succ, List.append_assoc] using hpairs
    exact (targetExtraTickStuckWitness
      stateCount row middle remainingBlocks hmiddle).prepend hpairs'

private def malformedCellStuckWitness17
    (left : Word ValidatorBlockSymbol)
    (bad : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (hblank : bad ≠ .blank) (hzero : bad ≠ .zero)
    (hone : bad ≠ .one) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 17 left (validatorCanonicalBlocks (bad :: rest))) := by
  cases bad with
  | blank => contradiction
  | zero => contradiction
  | one => contradiction
  | header =>
      exact canonicalLeafWitness 17 left .header rest
        (by decide) (by decide) (by decide) (by decide)
  | transition =>
      exact canonicalLeafWitness 17 left .transition rest
        (by decide) (by decide) (by decide) (by decide)
  | tick =>
      exact canonicalLeafWitness 17 left .tick rest
        (by decide) (by decide) (by decide) (by decide)
  | done =>
      exact canonicalLeafWitness 17 left .done rest
        (by decide) (by decide) (by decide) (by decide)
  | moveLeft =>
      exact canonicalLeafWitness 17 left .moveLeft rest
        (by decide) (by decide) (by decide) (by decide)
  | moveRight =>
      exact canonicalLeafWitness 17 left .moveRight rest
        (by decide) (by decide) (by decide) (by decide)

private def malformedCellStuckWitness18
    (left : Word ValidatorBlockSymbol)
    (bad : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (hblank : bad ≠ .blank) (hzero : bad ≠ .zero)
    (hone : bad ≠ .one) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 18 left (validatorCanonicalBlocks (bad :: rest))) := by
  cases bad with
  | blank => contradiction
  | zero => contradiction
  | one => contradiction
  | header =>
      exact canonicalLeafWitness 18 left .header rest
        (by decide) (by decide) (by decide) (by decide)
  | transition =>
      exact canonicalLeafWitness 18 left .transition rest
        (by decide) (by decide) (by decide) (by decide)
  | tick =>
      exact canonicalLeafWitness 18 left .tick rest
        (by decide) (by decide) (by decide) (by decide)
  | done =>
      exact canonicalLeafWitness 18 left .done rest
        (by decide) (by decide) (by decide) (by decide)
  | moveLeft =>
      exact canonicalLeafWitness 18 left .moveLeft rest
        (by decide) (by decide) (by decide) (by decide)
  | moveRight =>
      exact canonicalLeafWitness 18 left .moveRight rest
        (by decide) (by decide) (by decide) (by decide)

private def malformedDirectionStuckWitness19
    (left : Word ValidatorBlockSymbol)
    (bad : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (hleft : bad ≠ .moveLeft) (hright : bad ≠ .moveRight) :
    ValidatorBlockStuckWitness blockDescription Description
      (configuration 19 left (validatorCanonicalBlocks (bad :: rest))) := by
  cases bad with
  | moveLeft => contradiction
  | moveRight => contradiction
  | header =>
      exact canonicalLeafWitness 19 left .header rest
        (by decide) (by decide) (by decide) (by decide)
  | transition =>
      exact canonicalLeafWitness 19 left .transition rest
        (by decide) (by decide) (by decide) (by decide)
  | tick =>
      exact canonicalLeafWitness 19 left .tick rest
        (by decide) (by decide) (by decide) (by decide)
  | done =>
      exact canonicalLeafWitness 19 left .done rest
        (by decide) (by decide) (by decide) (by decide)
  | blank =>
      exact canonicalLeafWitness 19 left .blank rest
        (by decide) (by decide) (by decide) (by decide)
  | zero =>
      exact canonicalLeafWitness 19 left .zero rest
        (by decide) (by decide) (by decide) (by decide)
  | one =>
      exact canonicalLeafWitness 19 left .one rest
        (by decide) (by decide) (by decide) (by decide)

private def checkedRowOutcome
    (stateCount : Nat) (middle : Word ValidatorBlockSymbol)
    (tokens : Word MachineCodeSymbol)
    (hmiddle : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from middle) ->
        symbol ∈ corridorSymbols) :
    CheckedRowOutcome stateCount middle tokens := by
  cases natTokenView tokens with
  | malformed source bad rest htokens hbadTick hbadDone =>
      exact .stuck (by
        simpa [htokens] using
          sourceMalformedStuckWitness stateCount source bad rest middle
            hmiddle hbadTick hbadDone)
  | unterminated source htokens =>
      exact .stuck (by
        simpa [htokens] using
          sourceUnterminatedStuckWitness
            stateCount source middle hmiddle)
  | parsed source afterSource hsourceTokens =>
      by_cases hsourceBound : source < stateCount
      · let left17 := restoredSourceLeft stateCount source middle
        have hsourceCore := reaches_source_bound
          stateCount source middle
          (validatorCanonicalBlocks afterSource) hmiddle hsourceBound
        have hsourceRun :
            blockDescription.Reaches
              (configuration 8 (sourcePairLeft stateCount 0 middle)
                (validatorCanonicalBlocks tokens))
              (configuration 17 left17
                (validatorCanonicalBlocks afterSource)) := by
          simpa [hsourceTokens, left17,
            validatorCanonicalBlocks_encodeNatAppend,
            ValidatorHeaderBounds.validatorCanonicalBlocks_encodeNat,
            ValidatorHeaderBounds.natBlocks, List.append_assoc] using
              hsourceCore
        cases cellTokenView afterSource with
        | missing =>
            exact .stuck
              ((canonicalBlankWitness 17 left17
                (by decide) (by decide) (by decide) (by decide)).prepend
                  hsourceRun)
        | malformed bad rest hreadTokens hblank hzero hone =>
            have hwitness := malformedCellStuckWitness17
              left17 bad rest hblank hzero hone
            have hwitness' :
                ValidatorBlockStuckWitness blockDescription Description
                  (configuration 17 left17
                    (validatorCanonicalBlocks afterSource)) := by
              simpa [hreadTokens] using hwitness
            exact .stuck
              (hwitness'.prepend hsourceRun)
        | parsed read afterRead hreadTokens =>
            let left18 := List.append left17 [cellBlock read]
            have hreadCore := reaches_one_right
              (state := 17) (target := 18)
              (read := cellBlock read) (write := cellBlock read)
              (by
                cases read with
                | none => decide
                | some bit => cases bit <;> decide)
              left17 (validatorCanonicalBlocks afterRead)
            have hreadRun :
                blockDescription.Reaches
                  (configuration 17 left17
                    (validatorCanonicalBlocks afterSource))
                  (configuration 18 left18
                    (validatorCanonicalBlocks afterRead)) := by
              simpa [hreadTokens, canonicalBlocks_encodeCellAppend,
                left18] using hreadCore
            cases cellTokenView afterRead with
            | missing =>
                exact .stuck
                  ((canonicalBlankWitness 18 left18
                    (by decide) (by decide) (by decide) (by decide)).prepend
                      (hsourceRun.trans hreadRun))
            | malformed bad rest hwriteTokens hblank hzero hone =>
                have hwitness := malformedCellStuckWitness18
                  left18 bad rest hblank hzero hone
                have hwitness' :
                    ValidatorBlockStuckWitness blockDescription Description
                      (configuration 18 left18
                        (validatorCanonicalBlocks afterRead)) := by
                  simpa [hwriteTokens] using hwitness
                exact .stuck
                  (hwitness'.prepend (hsourceRun.trans hreadRun))
            | parsed write afterWrite hwriteTokens =>
                let left19 := List.append left18 [cellBlock write]
                have hwriteCore := reaches_one_right
                  (state := 18) (target := 19)
                  (read := cellBlock write) (write := cellBlock write)
                  (by
                    cases write with
                    | none => decide
                    | some bit => cases bit <;> decide)
                  left18 (validatorCanonicalBlocks afterWrite)
                have hwriteRun :
                    blockDescription.Reaches
                      (configuration 18 left18
                        (validatorCanonicalBlocks afterRead))
                      (configuration 19 left19
                        (validatorCanonicalBlocks afterWrite)) := by
                  simpa [hwriteTokens, canonicalBlocks_encodeCellAppend,
                    left19] using hwriteCore
                cases directionTokenView afterWrite with
                | missing =>
                    exact .stuck
                      ((canonicalBlankWitness 19 left19
                        (by decide) (by decide) (by decide) (by decide)).prepend
                          (hsourceRun.trans (hreadRun.trans hwriteRun)))
                | malformed bad rest hmoveTokens hleft hright =>
                    have hwitness := malformedDirectionStuckWitness19
                      left19 bad rest hleft hright
                    have hwitness' :
                        ValidatorBlockStuckWitness blockDescription Description
                          (configuration 19 left19
                            (validatorCanonicalBlocks afterWrite)) := by
                      simpa [hmoveTokens] using hwitness
                    exact .stuck
                      (hwitness'.prepend
                        (hsourceRun.trans (hreadRun.trans hwriteRun)))
                | parsed move afterMove hmoveTokens =>
                    let row : TransitionDescription :=
                      { source := source
                        read := read
                        write := write
                        move := move
                        target := 0 }
                    let left20 := List.append left19 [directionBlock move]
                    have hmoveCore := reaches_one_right
                      (state := 19) (target := 20)
                      (read := directionBlock move)
                      (write := directionBlock move)
                      (by cases move <;> decide)
                      left19 (validatorCanonicalBlocks afterMove)
                    have hmoveRun :
                        blockDescription.Reaches
                          (configuration 19 left19
                            (validatorCanonicalBlocks afterWrite))
                          (configuration 20 left20
                            (validatorCanonicalBlocks afterMove)) := by
                      simpa [hmoveTokens,
                        canonicalBlocks_encodeDirectionAppend,
                        left20] using hmoveCore
                    cases natTokenView afterMove with
                    | malformed target bad rest htargetTokens
                        hbadTick hbadDone =>
                        let parsedRow : TransitionDescription :=
                          { source := source
                            read := read
                            write := write
                            move := move
                            target := target }
                        have hleft20 :
                            left20 =
                              targetPairLeft stateCount 0 parsedRow middle := by
                          simp [left20, left19, left18, left17, parsedRow,
                            targetPairLeft, markedTicks, restoredSourceLeft,
                            List.append_assoc]
                        have hprefix :
                            blockDescription.Reaches
                              (configuration 8
                                (sourcePairLeft stateCount 0 middle)
                                (validatorCanonicalBlocks tokens))
                              (configuration 20
                                (targetPairLeft stateCount 0 parsedRow middle)
                                (validatorCanonicalBlocks afterMove)) := by
                          simpa [hleft20] using hsourceRun.trans
                            (hreadRun.trans (hwriteRun.trans hmoveRun))
                        have hwitness := targetMalformedStuckWitness
                          stateCount target bad rest parsedRow middle hmiddle
                          hbadTick hbadDone
                        have hwitness' :
                            ValidatorBlockStuckWitness
                              blockDescription Description
                              (configuration 20
                                (targetPairLeft stateCount 0 parsedRow middle)
                                (validatorCanonicalBlocks afterMove)) := by
                          simpa [htargetTokens] using hwitness
                        exact .stuck (hwitness'.prepend hprefix)
                    | unterminated target htargetTokens =>
                        let parsedRow : TransitionDescription :=
                          { source := source
                            read := read
                            write := write
                            move := move
                            target := target }
                        have hleft20 :
                            left20 =
                              targetPairLeft stateCount 0 parsedRow middle := by
                          simp [left20, left19, left18, left17, parsedRow,
                            targetPairLeft, markedTicks, restoredSourceLeft,
                            List.append_assoc]
                        have hprefix :
                            blockDescription.Reaches
                              (configuration 8
                                (sourcePairLeft stateCount 0 middle)
                                (validatorCanonicalBlocks tokens))
                              (configuration 20
                                (targetPairLeft stateCount 0 parsedRow middle)
                                (validatorCanonicalBlocks afterMove)) := by
                          simpa [hleft20] using hsourceRun.trans
                            (hreadRun.trans (hwriteRun.trans hmoveRun))
                        have hwitness := targetUnterminatedStuckWitness
                          stateCount target parsedRow middle hmiddle
                        have hwitness' :
                            ValidatorBlockStuckWitness
                              blockDescription Description
                              (configuration 20
                                (targetPairLeft stateCount 0 parsedRow middle)
                                (validatorCanonicalBlocks afterMove)) := by
                          simpa [htargetTokens] using hwitness
                        exact .stuck (hwitness'.prepend hprefix)
                    | parsed target rest htargetTokens =>
                        let parsedRow : TransitionDescription :=
                          { source := source
                            read := read
                            write := write
                            move := move
                            target := target }
                        have hleft20 :
                            left20 =
                              targetPairLeft stateCount 0 parsedRow middle := by
                          simp [left20, left19, left18, left17, parsedRow,
                            targetPairLeft, markedTicks, restoredSourceLeft,
                            List.append_assoc]
                        have hprefix :
                            blockDescription.Reaches
                              (configuration 8
                                (sourcePairLeft stateCount 0 middle)
                                (validatorCanonicalBlocks tokens))
                              (configuration 20
                                (targetPairLeft stateCount 0 parsedRow middle)
                                (validatorCanonicalBlocks afterMove)) := by
                          simpa [hleft20] using hsourceRun.trans
                            (hreadRun.trans (hwriteRun.trans hmoveRun))
                        by_cases htargetBound : target < stateCount
                        · have htargetCore := reaches_target_bound
                            stateCount parsedRow middle
                            (validatorCanonicalBlocks rest)
                            hmiddle (by simpa [parsedRow] using htargetBound)
                          have htargetRun :
                              blockDescription.Reaches
                                (configuration 20
                                  (targetPairLeft stateCount 0 parsedRow middle)
                                  (validatorCanonicalBlocks afterMove))
                                (configuration 0
                                  (restoredRowLeft
                                    stateCount target parsedRow middle)
                                  (.done :: validatorCanonicalBlocks rest)) := by
                            simpa [htargetTokens, parsedRow,
                              validatorCanonicalBlocks_encodeNatAppend,
                              ValidatorHeaderBounds.validatorCanonicalBlocks_encodeNat,
                              ValidatorHeaderBounds.natBlocks,
                              List.append_assoc] using htargetCore
                          exact .success
                            { row := parsedRow
                              rest := rest
                              tokens_eq := by
                                calc
                                  tokens = encodeNatAppend source afterSource :=
                                    hsourceTokens
                                  _ = encodeNatAppend source
                                      (encodeCellAppend read afterRead) := by
                                    rw [hreadTokens]
                                  _ = encodeNatAppend source
                                      (encodeCellAppend read
                                        (encodeCellAppend write afterWrite)) := by
                                    rw [hwriteTokens]
                                  _ = encodeNatAppend source
                                      (encodeCellAppend read
                                        (encodeCellAppend write
                                          (encodeDirectionAppend move afterMove))) := by
                                    rw [hmoveTokens]
                                  _ = transitionBodyAppend parsedRow rest := by
                                    rw [htargetTokens]
                                    rfl
                              source_lt := by
                                simpa [parsedRow] using hsourceBound
                              target_lt := by
                                simpa [parsedRow] using htargetBound
                              reaches := hprefix.trans htargetRun }
                        · have hwitness := targetBoundStuckWitness
                            stateCount parsedRow middle
                            (validatorCanonicalBlocks rest) hmiddle
                            (by simpa [parsedRow] using htargetBound)
                          have hwitness' :
                              ValidatorBlockStuckWitness
                                blockDescription Description
                                (configuration 20
                                  (targetPairLeft stateCount 0 parsedRow middle)
                                  (validatorCanonicalBlocks afterMove)) := by
                            simpa [htargetTokens, parsedRow,
                              validatorCanonicalBlocks_encodeNatAppend,
                              ValidatorHeaderBounds.validatorCanonicalBlocks_encodeNat,
                              ValidatorHeaderBounds.natBlocks,
                              List.append_assoc] using hwitness
                          exact .stuck (hwitness'.prepend hprefix)
      · have hwitness := sourceBoundStuckWitness
          stateCount source middle
          (validatorCanonicalBlocks afterSource) hmiddle hsourceBound
        exact .stuck (by
          simpa [hsourceTokens,
            validatorCanonicalBlocks_encodeNatAppend,
            ValidatorHeaderBounds.validatorCanonicalBlocks_encodeNat,
            ValidatorHeaderBounds.natBlocks,
            List.append_assoc] using hwitness)

private structure CheckedRowsSuccess
    (stateCount remaining : Nat)
    (tokens : Word MachineCodeSymbol) where
  rows : List TransitionDescription
  suffix : Word MachineCodeSymbol
  count_eq : rows.length = remaining
  tokens_eq : tokens = encodeTransitionsAppend rows suffix
  bounds : forall row : TransitionDescription,
    row ∈ rows -> row.source < stateCount ∧ row.target < stateCount

private inductive CheckedRowsOutcome
    (stateCount start halt processed remaining : Nat)
    (bridge : Word ValidatorBlockSymbol)
    (tokens : Word MachineCodeSymbol) where
  | success : CheckedRowsSuccess stateCount remaining tokens ->
      CheckedRowsOutcome stateCount start halt processed remaining bridge tokens
  | stuck : ValidatorBlockStuckWitness blockDescription Description
      (configuration 0
        (loopLeftBlocks stateCount start halt processed remaining bridge)
        (.done :: validatorCanonicalBlocks tokens)) ->
      CheckedRowsOutcome stateCount start halt processed remaining bridge tokens

private def checkedRowsOutcome
    (stateCount start halt processed remaining : Nat)
    (bridge : Word ValidatorBlockSymbol)
    (tokens : Word MachineCodeSymbol)
    (hbridge : forall symbol : ValidatorBlockSymbol,
      symbol ∈ (show List ValidatorBlockSymbol from bridge) ->
        symbol ∈ canonicalCorridorSymbols) :
    CheckedRowsOutcome
      stateCount start halt processed remaining bridge tokens :=
  match remaining with
  | 0 =>
      .success
        { rows := []
          suffix := tokens
          count_eq := rfl
          tokens_eq := rfl
          bounds := by simp }
  | Nat.succ remaining =>
      let selectedLeft := List.append
        (loopLeftBlocks stateCount start halt (processed + 1)
          remaining bridge)
        [.done]
      have hselect := reaches_select_counted_boundary
        stateCount start halt processed remaining bridge
        (validatorCanonicalBlocks tokens) hbridge
      have hselect' : blockDescription.Reaches
          (configuration 0
            (loopLeftBlocks stateCount start halt processed
              (Nat.succ remaining) bridge)
            (.done :: validatorCanonicalBlocks tokens))
          (configuration 7 selectedLeft
            (validatorCanonicalBlocks tokens)) := by
        simpa [selectedLeft, Nat.succ_eq_add_one] using hselect
      match tokens with
      | [] =>
          .stuck
            ((canonicalBlankWitness 7 selectedLeft
              (by decide) (by decide) (by decide) (by decide)).prepend
                hselect')
      | symbol :: body =>
          if htransition : symbol = MachineCodeSymbol.transition then
            by
              subst symbol
              let middle := rowMiddleBlocks start halt (processed + 1)
                remaining bridge
              have htransitionCore := reaches_one_right
                (state := 7) (target := 8)
                (read := ValidatorBlockSymbol.transition)
                (write := ValidatorBlockSymbol.marker001)
                (by decide) selectedLeft
                (validatorCanonicalBlocks body)
              have hselectedLeft :
                  List.append selectedLeft [.marker001] =
                    sourcePairLeft stateCount 0 middle := by
                simp [selectedLeft, middle, loopLeftBlocks,
                  rowMiddleBlocks, fixedPrefixBlocks, sourcePairLeft,
                  markedTicks, ValidatorHeaderBounds.natBlocks,
                  List.append_assoc]
              have htransitionRun : blockDescription.Reaches
                  (configuration 7 selectedLeft
                    (validatorCanonicalBlocks
                      (.transition :: body)))
                  (configuration 8
                    (sourcePairLeft stateCount 0 middle)
                    (validatorCanonicalBlocks body)) := by
                rw [hselectedLeft] at htransitionCore
                simpa [validatorCanonicalBlocks,
                  ValidatorBlockSymbol.ofMachineCodeSymbol] using
                  htransitionCore
              have hprefix := hselect'.trans htransitionRun
              have hmiddle : forall candidate : ValidatorBlockSymbol,
                  candidate ∈
                      (show List ValidatorBlockSymbol from middle) ->
                    candidate ∈ corridorSymbols := by
                exact rowMiddleBlocks_mem_corridor
                  start halt (processed + 1) remaining bridge hbridge
              cases checkedRowOutcome stateCount middle body hmiddle with
              | stuck hwitness =>
                  exact .stuck (hwitness.prepend hprefix)
              | success checked =>
                  let nextBridge :=
                    List.append (List.append bridge [.done])
                      (rowBodyBlocks checked.row)
                  have hnextBridge : forall candidate : ValidatorBlockSymbol,
                      candidate ∈
                          (show List ValidatorBlockSymbol from nextBridge) ->
                        candidate ∈ canonicalCorridorSymbols := by
                    exact extendedBridge_mem_canonical
                      checked.row bridge hbridge
                  cases checkedRowsOutcome
                      stateCount start halt (processed + 1) remaining
                      nextBridge checked.rest hnextBridge with
                  | stuck hwitness =>
                      have hrowRun : blockDescription.Reaches
                          (configuration 0
                            (loopLeftBlocks stateCount start halt processed
                              (Nat.succ remaining) bridge)
                            (.done :: validatorCanonicalBlocks
                              (.transition :: body)))
                          (configuration 0
                            (loopLeftBlocks stateCount start halt
                              (processed + 1) remaining nextBridge)
                            (.done ::
                              validatorCanonicalBlocks checked.rest)) := by
                        have hrun := hprefix.trans checked.reaches
                        have hrestored :
                            restoredRowLeft stateCount checked.row.target
                                checked.row middle =
                              loopLeftBlocks stateCount start halt
                                (processed + 1) remaining nextBridge := by
                          simpa [middle, nextBridge] using
                            restoredRowLeft_eq_next_loop
                              stateCount start halt processed remaining
                              checked.row bridge
                        rw [hrestored] at hrun
                        simpa [Nat.succ_eq_add_one] using hrun
                      exact .stuck (hwitness.prepend hrowRun)
                  | success checkedRest =>
                      exact .success
                        { rows := checked.row :: checkedRest.rows
                          suffix := checkedRest.suffix
                          count_eq := by
                            simp [checkedRest.count_eq]
                          tokens_eq := by
                            simp [encodeTransitionsAppend,
                              encodeTransitionAppend,
                              transitionBodyAppend, checked.tokens_eq,
                              checkedRest.tokens_eq]
                          bounds := by
                            intro candidate hcandidate
                            rcases List.mem_cons.mp hcandidate with
                              rfl | hcandidate
                            · exact ⟨checked.source_lt, checked.target_lt⟩
                            · exact checkedRest.bounds candidate hcandidate }
          else
            by
              have hleafNone :
                  Description.lookupTransition
                      (validatorBlockLeafState 7
                        (ValidatorBlockSymbol.ofMachineCodeSymbol symbol))
                      (some
                        (ValidatorBlockSymbol.ofMachineCodeSymbol
                          symbol).fourthBit) = none := by
                cases symbol with
                | header => decide
                | transition => exact (htransition rfl).elim
                | tick => decide
                | done => decide
                | blank => decide
                | zero => decide
                | one => decide
                | moveLeft => decide
                | moveRight => decide
              have hwitness := canonicalLeafWitness
                7 selectedLeft symbol body
                (by decide) (by decide) hleafNone (by
                  cases symbol <;> decide)
              exact .stuck (hwitness.prepend hselect')
termination_by remaining

/-- Constructive result of inverting the complete declared-count loop. -/
inductive CountedRowsInversionOutcome
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) : Type where
  | accepted
      (rows : List TransitionDescription)
      (suffix : Word MachineCodeSymbol)
      (count_eq : rows.length = transitionCount)
      (tokens_eq : tokens = encodeTransitionsAppend rows suffix)
      (bounds : forall row : TransitionDescription,
        row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
      CountedRowsInversionOutcome
        stateCount start halt transitionCount tokens
  | stuck
      (witness : ValidatorBlockStuckWitness blockDescription Description
        (configuration 0
          (loopLeftBlocks stateCount start halt 0 transitionCount [])
          (.done :: validatorCanonicalBlocks tokens))) :
      CountedRowsInversionOutcome
        stateCount start halt transitionCount tokens

/-- The declared-count loop either decodes exactly that many bounded rows or
reaches a concrete nonhalting compiler state. -/
def checkedRowsInversion
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    CountedRowsInversionOutcome
      stateCount start halt transitionCount tokens := by
  cases checkedRowsOutcome
      stateCount start halt 0 transitionCount [] tokens (by simp) with
  | success checked =>
      exact .accepted checked.rows checked.suffix checked.count_eq
        checked.tokens_eq checked.bounds
  | stuck hwitness =>
      exact .stuck hwitness

end ValidatorCountedRows
end SelfHaltingRecognizer
end Computability
end FoC

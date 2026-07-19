import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PrefixHalting
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.HaltStoppedMachine
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine.Compiler
set_option doc.verso true
/-!
# Finite code-alphabet lowering

The concrete universal-prefix runner is already a finite
{name (full := FoC.Computability.TuringMachine)}`TuringMachine`, but it runs on
the nine-symbol
{name (full := FoC.Computability.MachineCodeSymbol)}`MachineCodeSymbol`
alphabet.  The Section 5.3 endpoint instead requires a Boolean
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`.
This module supplies
the two explicit finite bridges used by the self-halting recognizer:

1. enumerate any finite Boolean machine into a literal description table; and
2. simulate one code-symbol tape cell by one aligned four-bit Boolean block.

The construction is deliberately local to the recognizer campaign.  It does
not assert an unrestricted semantic compiler Principle.
-/
namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace CodeAlphabetLowering
open Languages
open MachineDescription
/-!
## Finite Boolean machines as description tables
-/

private def boolTapeCellFinite : Foundation.FiniteType (Option Bool) :=
  Foundation.FiniteType.option Foundation.FiniteType.bool
private def finiteBoolMachineRow? [DecidableEq state]
    (M : TuringMachine Bool state)
    (entry : state × Option Bool) : Option TransitionDescription :=
  if entry.1 = M.halt then
    none
  else
    match M.transition entry.1 entry.2 with
    | none => none
    | some (write, move, target) =>
        some
          { source :=
              (Foundation.FiniteType.indexOfDecidable
                M.statesFinite entry.1).val
            read := entry.2
            write := write
            move := move
            target :=
              (Foundation.FiniteType.indexOfDecidable
                M.statesFinite target).val }

private def finiteBoolMachineRows [DecidableEq state]
    (M : TuringMachine Bool state) : List TransitionDescription :=
  (Foundation.FiniteType.pairElems
      M.statesFinite.elems boolTapeCellFinite.elems).filterMap
    (finiteBoolMachineRow? M)

private def finiteBoolMachineDescription [DecidableEq state]
    (M : TuringMachine Bool state) : MachineDescription where
  stateCount := M.statesFinite.elems.length
  start :=
    (Foundation.FiniteType.indexOfDecidable M.statesFinite M.start).val
  halt :=
    (Foundation.FiniteType.indexOfDecidable M.statesFinite M.halt).val
  transitions := finiteBoolMachineRows M

private theorem finite_index_injective [DecidableEq alpha]
    (finite : Foundation.FiniteType alpha) :
    Function.Injective
      (fun value =>
        (Foundation.FiniteType.indexOfDecidable finite value).val) := by
  intro left right heq
  have hfin :
      Foundation.FiniteType.indexOfDecidable finite left =
        Foundation.FiniteType.indexOfDecidable finite right := by
    exact Fin.ext heq
  have hvalue := congrArg (Foundation.FiniteType.valueOf finite) hfin
  simpa [Foundation.FiniteType.valueOf_indexOfDecidable] using hvalue

private theorem finiteBoolMachineRow?_eq_some_iff [DecidableEq state]
    {M : TuringMachine Bool state}
    {entry : state × Option Bool} {row : TransitionDescription} :
    finiteBoolMachineRow? M entry = some row <->
      entry.1 ≠ M.halt ∧
        exists write : Option Bool,
        exists move : Direction,
        exists target : state,
          M.transition entry.1 entry.2 = some (write, move, target) ∧
          row =
            { source :=
                (Foundation.FiniteType.indexOfDecidable
                  M.statesFinite entry.1).val
              read := entry.2
              write := write
              move := move
              target :=
                (Foundation.FiniteType.indexOfDecidable
                  M.statesFinite target).val } := by
  unfold finiteBoolMachineRow?
  by_cases hhalt : entry.1 = M.halt
  · simp [hhalt]
  · rw [if_neg hhalt]
    cases htransition : M.transition entry.1 entry.2 with
    | none =>
        simp [hhalt]
    | some action =>
        rcases action with ⟨write, move, target⟩
        simp only
        constructor
        · intro hrow
          have heq := Option.some.inj hrow
          exact ⟨hhalt, write, move, target, rfl, heq.symm⟩
        · rintro ⟨_hnotHalt, otherWrite, otherMove, otherTarget,
            hotherTransition, rfl⟩
          cases hotherTransition
          rfl

private theorem finiteBoolMachineRow_mem [DecidableEq state]
    {M : TuringMachine Bool state}
    {source : state} {read write : Option Bool}
    {move : Direction} {target : state}
    (hsource : source ≠ M.halt)
    (htransition : M.transition source read =
      some (write, move, target)) :
    ({ source :=
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite source).val
       read := read
       write := write
       move := move
       target :=
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite target).val } :
      TransitionDescription) ∈ finiteBoolMachineRows M := by
  unfold finiteBoolMachineRows
  apply List.mem_filterMap.mpr
  refine ⟨(source, read), ?_, ?_⟩
  · exact Foundation.FiniteType.pair_mem
      (M.statesFinite.complete source)
      (boolTapeCellFinite.complete read)
  · simp [finiteBoolMachineRow?, hsource, htransition]

private theorem finiteBoolMachineRow_mem_inv [DecidableEq state]
    {M : TuringMachine Bool state} {row : TransitionDescription}
    (hrow : row ∈ finiteBoolMachineRows M) :
    exists source : state,
    exists read write : Option Bool,
    exists move : Direction,
    exists target : state,
      source ≠ M.halt ∧
      M.transition source read = some (write, move, target) ∧
      row =
        { source :=
            (Foundation.FiniteType.indexOfDecidable
              M.statesFinite source).val
          read := read
          write := write
          move := move
          target :=
            (Foundation.FiniteType.indexOfDecidable
              M.statesFinite target).val } := by
  unfold finiteBoolMachineRows at hrow
  rcases List.mem_filterMap.mp hrow with ⟨entry, _hentry, hmap⟩
  rcases (finiteBoolMachineRow?_eq_some_iff.mp hmap) with
    ⟨hsource, write, move, target, htransition, rfl⟩
  exact ⟨entry.1, entry.2, write, move, target,
    hsource, htransition, rfl⟩

private theorem finiteBoolMachineDescription_deterministic [DecidableEq state]
    (M : TuringMachine Bool state) :
    (finiteBoolMachineDescription M).Deterministic := by
  intro left right hleft hright hkey
  rcases finiteBoolMachineRow_mem_inv hleft with
    ⟨leftSource, leftRead, leftWrite, leftMove, leftTarget,
      _hleftHalt, hleftTransition, rfl⟩
  rcases finiteBoolMachineRow_mem_inv hright with
    ⟨rightSource, rightRead, rightWrite, rightMove, rightTarget,
      _hrightHalt, hrightTransition, rfl⟩
  have hsourceIndex := hkey.1
  have hsource : leftSource = rightSource :=
    finite_index_injective M.statesFinite hsourceIndex
  have hread : leftRead = rightRead := hkey.2
  subst rightSource
  subst rightRead
  rw [hleftTransition] at hrightTransition
  cases hrightTransition
  exact ⟨rfl, rfl, rfl⟩

private theorem finiteBoolMachineDescription_wellFormed [DecidableEq state]
    (M : TuringMachine Bool state) :
    (finiteBoolMachineDescription M).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_,
    finiteBoolMachineDescription_deterministic M⟩
  · have hstart := M.statesFinite.complete M.start
    change 0 < M.statesFinite.elems.length
    exact List.length_pos_of_mem hstart
  · exact (Foundation.FiniteType.indexOfDecidable
      M.statesFinite M.start).isLt
  · exact (Foundation.FiniteType.indexOfDecidable
      M.statesFinite M.halt).isLt
  · intro row hrow
    rcases finiteBoolMachineRow_mem_inv hrow with
      ⟨source, read, write, move, target,
        _hsource, _htransition, rfl⟩
    exact ⟨(Foundation.FiniteType.indexOfDecidable
      M.statesFinite source).isLt,
      (Foundation.FiniteType.indexOfDecidable
        M.statesFinite target).isLt⟩

private theorem finiteBoolMachineDescription_haltTransitionFree
    [DecidableEq state]
    (M : TuringMachine Bool state) :
    (finiteBoolMachineDescription M).HaltTransitionFree := by
  intro row hrow
  rcases finiteBoolMachineRow_mem_inv hrow with
    ⟨source, read, write, move, target,
      hsource, _htransition, rfl⟩
  intro heq
  apply hsource
  exact finite_index_injective M.statesFinite heq

private theorem finiteBoolMachineDescription_subroutineReady
    [DecidableEq state]
    (M : TuringMachine Bool state) :
    (finiteBoolMachineDescription M).SubroutineReady :=
  ⟨finiteBoolMachineDescription_wellFormed M,
    finiteBoolMachineDescription_haltTransitionFree M⟩

private def finiteBoolMachineConfig [DecidableEq state]
    (M : TuringMachine Bool state)
    (configuration : TuringMachine.Configuration Bool state) :
    MachineDescription.Configuration :=
  { state :=
      (Foundation.FiniteType.indexOfDecidable
        M.statesFinite configuration.state).val
    tape := configuration.tape }

private theorem finiteBoolMachineDescription_lookup_of_transition
    [DecidableEq state]
    {M : TuringMachine Bool state}
    {source : state} {read write : Option Bool}
    {move : Direction} {target : state}
    (hsource : source ≠ M.halt)
    (htransition : M.transition source read =
      some (write, move, target)) :
    (finiteBoolMachineDescription M).lookupTransition
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite source).val read =
      some
        { source :=
            (Foundation.FiniteType.indexOfDecidable
              M.statesFinite source).val
          read := read
          write := write
          move := move
          target :=
            (Foundation.FiniteType.indexOfDecidable
              M.statesFinite target).val } := by
  exact lookupTransition_eq_some_of_mem_deterministic
    (finiteBoolMachineDescription_deterministic M)
    (finiteBoolMachineRow_mem hsource htransition)

private theorem finiteBoolMachineDescription_lookup_none_of_transition_none
    [DecidableEq state]
    {M : TuringMachine Bool state}
    {source : state} {read : Option Bool}
    (htransition : M.transition source read = none) :
    (finiteBoolMachineDescription M).lookupTransition
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite source).val read =
      none := by
  cases hlookup :
      (finiteBoolMachineDescription M).lookupTransition
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite source).val read with
  | none => rfl
  | some row =>
      have hmem := MachineDescription.lookupTransition_mem hlookup
      rcases finiteBoolMachineRow_mem_inv hmem with
        ⟨otherSource, otherRead, write, move, target,
          _hotherHalt, hotherTransition, hrow⟩
      have hmatches := MachineDescription.lookupTransition_matches hlookup
      rw [hrow] at hmatches
      have hsource : otherSource = source := by
        apply finite_index_injective M.statesFinite
        exact hmatches.1
      have hread : otherRead = read := hmatches.2
      subst otherSource
      subst otherRead
      rw [htransition] at hotherTransition
      cases hotherTransition

private theorem finiteBoolMachineDescription_lookup_none_of_halt
    [DecidableEq state]
    (M : TuringMachine Bool state) (read : Option Bool) :
    (finiteBoolMachineDescription M).lookupTransition
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite M.halt).val read =
      none := by
  cases hlookup :
      (finiteBoolMachineDescription M).lookupTransition
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite M.halt).val read with
  | none => rfl
  | some row =>
      have hmem := MachineDescription.lookupTransition_mem hlookup
      rcases finiteBoolMachineRow_mem_inv hmem with
        ⟨source, sourceRead, write, move, target,
          hsource, _htransition, hrow⟩
      have hmatches := MachineDescription.lookupTransition_matches hlookup
      rw [hrow] at hmatches
      exact False.elim
        (hsource (finite_index_injective M.statesFinite hmatches.1))

private theorem finiteBoolMachineDescription_stepConfig
    [DecidableEq state]
    (M : TuringMachine Bool state)
    (configuration : TuringMachine.Configuration Bool state) :
    (finiteBoolMachineDescription M).stepConfig
        (finiteBoolMachineConfig M configuration) =
      if configuration.state = M.halt then
        none
      else
        Option.map (finiteBoolMachineConfig M)
          (M.stepConfig configuration) := by
  rcases configuration with ⟨state, tape⟩
  by_cases hhalt : state = M.halt
  · subst state
    simp [MachineDescription.stepConfig, finiteBoolMachineConfig,
      finiteBoolMachineDescription_lookup_none_of_halt]
  · cases htransition :
      M.transition state (Tape.read tape) with
    | none =>
        have hlookup :=
          finiteBoolMachineDescription_lookup_none_of_transition_none
            htransition
        simp [MachineDescription.stepConfig, TuringMachine.stepConfig,
          finiteBoolMachineConfig, hhalt, htransition, hlookup]
    | some action =>
        rcases action with ⟨write, move, target⟩
        have hlookup :=
          finiteBoolMachineDescription_lookup_of_transition
            hhalt htransition
        simp [MachineDescription.stepConfig, TuringMachine.stepConfig,
          finiteBoolMachineConfig, hhalt, htransition, hlookup]

private theorem finiteBoolMachineDescription_stepConfig_stopped
    [DecidableEq state]
    (M : TuringMachine Bool state)
    (configuration : TuringMachine.Configuration Bool state) :
    (finiteBoolMachineDescription M).stepConfig
        (finiteBoolMachineConfig M configuration) =
      Option.map (finiteBoolMachineConfig M)
        ((haltStoppedMachine M).stepConfig configuration) := by
  rw [finiteBoolMachineDescription_stepConfig,
    haltStoppedMachine_stepConfig]
  by_cases hhalt : configuration.state = M.halt <;> simp [hhalt]

private theorem finiteBoolMachineDescription_runConfig_stopped
    [DecidableEq state]
    (M : TuringMachine Bool state) (steps : Nat)
    (configuration : TuringMachine.Configuration Bool state) :
    (finiteBoolMachineDescription M).runConfig steps
        (finiteBoolMachineConfig M configuration) =
      finiteBoolMachineConfig M
        ((haltStoppedMachine M).runConfigBounded steps configuration) := by
  induction steps generalizing configuration with
  | zero => rfl
  | succ steps ih =>
      rw [MachineDescription.runConfig,
        TuringMachine.runConfigBounded,
        finiteBoolMachineDescription_stepConfig_stopped]
      cases hstep : (haltStoppedMachine M).stepConfig configuration with
      | none => rfl
      | some next =>
          simpa using ih next

private theorem finiteBoolMachineDescription_haltsFromTape_iff
    [DecidableEq state]
    (M : TuringMachine Bool state) (source : Tape Bool) :
    (exists target : Tape Bool,
      (finiteBoolMachineDescription M).HaltsFromTape source target) <->
      TuringMachine.HaltsFrom M
        { state := M.start, tape := source } := by
  rw [← haltStoppedMachine_haltsFrom_iff]
  constructor
  · rintro ⟨_target, steps, hhalt, _htape⟩
    let initial : TuringMachine.Configuration Bool state :=
      { state := M.start, tape := source }
    have hrun := finiteBoolMachineDescription_runConfig_stopped
      M steps initial
    have hstate := congrArg MachineDescription.Configuration.state hrun
    have hindexed :
        (Foundation.FiniteType.indexOfDecidable M.statesFinite
          ((haltStoppedMachine M).runConfigBounded steps initial).state).val =
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite M.halt).val := by
      exact hstate.symm.trans hhalt
    have hstopped :
        ((haltStoppedMachine M).runConfigBounded steps initial).state =
          M.halt :=
      finite_index_injective M.statesFinite hindexed
    exact ⟨(haltStoppedMachine M).runConfigBounded steps initial,
      runConfigBounded_computes (haltStoppedMachine M) steps initial,
      hstopped⟩
  · rintro ⟨final, hcomputes, hhalt⟩
    rcases TuringMachine.computes_to_computesIn hcomputes with
      ⟨steps, hcomputesIn⟩
    refine ⟨final.tape, steps, ?_⟩
    let initial : TuringMachine.Configuration Bool state :=
      { state := M.start, tape := source }
    have hbounded :
        (haltStoppedMachine M).runConfigBounded steps initial = final :=
      runConfigBounded_eq_of_computesIn hcomputesIn
    change
      ((finiteBoolMachineDescription M).runConfig steps
        { state := (finiteBoolMachineDescription M).start,
          tape := source }).state =
          (finiteBoolMachineDescription M).halt ∧
      ((finiteBoolMachineDescription M).runConfig steps
        { state := (finiteBoolMachineDescription M).start,
          tape := source }).tape = final.tape
    rw [show
      (MachineDescription.Configuration.mk
        (finiteBoolMachineDescription M).start source) =
        finiteBoolMachineConfig M initial by rfl]
    rw [finiteBoolMachineDescription_runConfig_stopped, hbounded]
    constructor
    · change
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite final.state).val =
        (Foundation.FiniteType.indexOfDecidable
          M.statesFinite M.halt).val
      have hhalt' : final.state = M.halt := by
        simpa [TuringMachine.Halted, haltStoppedMachine] using hhalt
      rw [hhalt']
    · rfl

private theorem finiteBoolMachineDescription_haltsOnInput_iff
    [DecidableEq state]
    (M : TuringMachine Bool state) (input : Word Bool) :
    (finiteBoolMachineDescription M).HaltsOnInput input <->
      TuringMachine.HaltsOnInput M input := by
  constructor
  · rintro ⟨steps, hhalt⟩
    apply (finiteBoolMachineDescription_haltsFromTape_iff
      M (Tape.input input)).mp
    refine ⟨((finiteBoolMachineDescription M).runConfig steps
      ((finiteBoolMachineDescription M).initial input)).tape,
      steps, hhalt, rfl⟩
  · intro hhalt
    rcases (finiteBoolMachineDescription_haltsFromTape_iff
        M (Tape.input input)).mpr
        (by simpa [TuringMachine.HaltsOnInput, TuringMachine.initial]
          using hhalt) with
      ⟨_target, steps, hstate, _htape⟩
    exact ⟨steps, hstate⟩

/-!
## Four-bit simulation of the code alphabet

Every logical code cell occupies four Boolean cells.  A logical tape blank is
represented by four physical blanks.  Root controls are aligned with the first
cell of a block; the remaining controls decode, rewrite, and move by one whole
block.  Only root controls can be the designated halt.
-/

private def codeCellBit0 : Option MachineCodeSymbol -> Option Bool
  | none => none
  | some symbol => some
      (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).firstBit

private def codeCellBit1 : Option MachineCodeSymbol -> Option Bool
  | none => none
  | some symbol => some
      (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).secondBit

private def codeCellBit2 : Option MachineCodeSymbol -> Option Bool
  | none => none
  | some symbol => some
      (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).thirdBit

private def codeCellBit3 : Option MachineCodeSymbol -> Option Bool
  | none => none
  | some symbol => some
      (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).fourthBit

private def codeCellBits
    (cell : Option MachineCodeSymbol) : List (Option Bool) :=
  [codeCellBit0 cell, codeCellBit1 cell,
    codeCellBit2 cell, codeCellBit3 cell]

private theorem codeCellBits_some (symbol : MachineCodeSymbol) :
    codeCellBits (some symbol) =
      (encodeCodeSymbolAsInput symbol).map some := by
  cases symbol <;> rfl

private theorem codeCellBits_none :
    codeCellBits (none : Option MachineCodeSymbol) =
      [none, none, none, none] := by
  rfl

private def decodeCodeBits
    (b0 b1 b2 b3 : Bool) : Option MachineCodeSymbol :=
  match b0, b1, b2, b3 with
  | false, false, false, false => some .header
  | false, false, false, true => some .transition
  | false, false, true, false => some .tick
  | false, false, true, true => some .done
  | false, true, false, false => some .blank
  | false, true, false, true => some .zero
  | false, true, true, false => some .one
  | false, true, true, true => some .moveLeft
  | true, false, false, false => some .moveRight
  | _, _, _, _ => none

private theorem decodeCodeBits_components (symbol : MachineCodeSymbol) :
    decodeCodeBits
        (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).firstBit
        (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).secondBit
        (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).thirdBit
        (ValidatorBlockSymbol.ofMachineCodeSymbol symbol).fourthBit =
      some symbol := by
  cases symbol <;> rfl

private structure BlockStepContext (state : Type) where
  source : state
  read : Option MachineCodeSymbol
  write : Option MachineCodeSymbol
  move : Direction
  target : state
deriving DecidableEq

private def directionFinite : Foundation.FiniteType Direction where
  elems := [Direction.left, Direction.right]
  complete := by
    intro direction
    cases direction <;> simp

private def codeTapeCellFinite :
    Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite

private def blockStepContextDataFinite
    (stateFinite : Foundation.FiniteType state) :
    Foundation.FiniteType
      (state × (Option MachineCodeSymbol ×
        (Option MachineCodeSymbol × (Direction × state)))) :=
  Foundation.FiniteType.prod stateFinite
    (Foundation.FiniteType.prod codeTapeCellFinite
      (Foundation.FiniteType.prod codeTapeCellFinite
        (Foundation.FiniteType.prod directionFinite stateFinite)))

private def BlockStepContext.ofData
    (data : state × (Option MachineCodeSymbol ×
      (Option MachineCodeSymbol × (Direction × state)))) :
    BlockStepContext state :=
  { source := data.1
    read := data.2.1
    write := data.2.2.1
    move := data.2.2.2.1
    target := data.2.2.2.2 }

private def blockStepContextFinite
    (stateFinite : Foundation.FiniteType state) :
    Foundation.FiniteType (BlockStepContext state) where
  elems := (blockStepContextDataFinite stateFinite).elems.map
    BlockStepContext.ofData
  complete := by
    intro context
    let data : state × (Option MachineCodeSymbol ×
        (Option MachineCodeSymbol × (Direction × state))) :=
      (context.source,
        (context.read, (context.write, (context.move, context.target))))
    apply List.mem_map.mpr
    refine ⟨data, (blockStepContextDataFinite stateFinite).complete data, ?_⟩
    cases context
    rfl

private inductive BlockControl (state : Type) where
  | root (logical : state)
  | decode1 (logical : state) (b0 : Bool)
  | decode2 (logical : state) (b0 b1 : Bool)
  | decode3 (logical : state) (b0 b1 b2 : Bool)
  | back2 (context : BlockStepContext state)
  | back1 (context : BlockStepContext state)
  | write0 (context : BlockStepContext state)
  | write1 (context : BlockStepContext state)
  | write2 (context : BlockStepContext state)
  | write3 (context : BlockStepContext state)
  | left0 (context : BlockStepContext state)
  | left1 (context : BlockStepContext state)
  | left2 (context : BlockStepContext state)
  | left3 (context : BlockStepContext state)
  | left4 (context : BlockStepContext state)
  | left5 (context : BlockStepContext state)
deriving DecidableEq

namespace BlockControl

private def stateBoolFinite
    (stateFinite : Foundation.FiniteType state) :
    Foundation.FiniteType (state × Bool) :=
  Foundation.FiniteType.prod stateFinite Foundation.FiniteType.bool

private def stateBool2Finite
    (stateFinite : Foundation.FiniteType state) :
    Foundation.FiniteType (state × (Bool × Bool)) :=
  Foundation.FiniteType.prod stateFinite
    (Foundation.FiniteType.prod
      Foundation.FiniteType.bool Foundation.FiniteType.bool)

private def stateBool3Finite
    (stateFinite : Foundation.FiniteType state) :
    Foundation.FiniteType (state × (Bool × (Bool × Bool))) :=
  Foundation.FiniteType.prod stateFinite
    (Foundation.FiniteType.prod Foundation.FiniteType.bool
      (Foundation.FiniteType.prod
        Foundation.FiniteType.bool Foundation.FiniteType.bool))

private def elems
    (stateFinite : Foundation.FiniteType state) : List (BlockControl state) :=
  stateFinite.elems.map root ++
  (stateBoolFinite stateFinite).elems.map
    (fun value => decode1 value.1 value.2) ++
  (stateBool2Finite stateFinite).elems.map
    (fun value => decode2 value.1 value.2.1 value.2.2) ++
  (stateBool3Finite stateFinite).elems.map
    (fun value => decode3 value.1 value.2.1 value.2.2.1 value.2.2.2) ++
  (blockStepContextFinite stateFinite).elems.map back2 ++
  (blockStepContextFinite stateFinite).elems.map back1 ++
  (blockStepContextFinite stateFinite).elems.map write0 ++
  (blockStepContextFinite stateFinite).elems.map write1 ++
  (blockStepContextFinite stateFinite).elems.map write2 ++
  (blockStepContextFinite stateFinite).elems.map write3 ++
  (blockStepContextFinite stateFinite).elems.map left0 ++
  (blockStepContextFinite stateFinite).elems.map left1 ++
  (blockStepContextFinite stateFinite).elems.map left2 ++
  (blockStepContextFinite stateFinite).elems.map left3 ++
  (blockStepContextFinite stateFinite).elems.map left4 ++
  (blockStepContextFinite stateFinite).elems.map left5

private def finite
    (stateFinite : Foundation.FiniteType state) :
    Foundation.FiniteType (BlockControl state) where
  elems := elems stateFinite
  complete := by
    intro control
    cases control with
    | root logical =>
        simp [elems, stateFinite.complete logical]
    | decode1 logical b0 =>
        have h := (stateBoolFinite stateFinite).complete (logical, b0)
        simpa [elems] using h
    | decode2 logical b0 b1 =>
        have h := (stateBool2Finite stateFinite).complete
          (logical, (b0, b1))
        have hmem :
            decode2 logical b0 b1 ∈
              (stateBool2Finite stateFinite).elems.map
                (fun value => decode2 value.1 value.2.1 value.2.2) :=
          List.mem_map.mpr ⟨(logical, (b0, b1)), h, rfl⟩
        unfold elems
        simp only [List.mem_append]
        simp only [hmem, or_true, true_or]
    | decode3 logical b0 b1 b2 =>
        have h := (stateBool3Finite stateFinite).complete
          (logical, (b0, (b1, b2)))
        have hmem :
            decode3 logical b0 b1 b2 ∈
              (stateBool3Finite stateFinite).elems.map
                (fun value =>
                  decode3 value.1 value.2.1 value.2.2.1 value.2.2.2) :=
          List.mem_map.mpr ⟨(logical, (b0, (b1, b2))), h, rfl⟩
        unfold elems
        simp only [List.mem_append]
        simp only [hmem, or_true, true_or]
    | back2 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | back1 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | write0 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | write1 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | write2 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | write3 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | left0 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | left1 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | left2 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | left3 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | left4 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]
    | left5 context =>
        simp [elems, (blockStepContextFinite stateFinite).complete context]

end BlockControl

private def keepExpected
    (expected actual : Option Bool) (move : Direction)
    (target : BlockControl state) :
    Option (Option Bool × Direction × BlockControl state) :=
  if actual = expected then some (actual, move, target) else none

private def writeExpected
    (expected actual write : Option Bool) (move : Direction)
    (target : BlockControl state) :
    Option (Option Bool × Direction × BlockControl state) :=
  if actual = expected then some (write, move, target) else none

private def blockContext
    (source : state) (read write : Option MachineCodeSymbol)
    (move : Direction) (target : state) : BlockStepContext state :=
  { source := source, read := read, write := write,
    move := move, target := target }

private def codeBlockTransition [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    BlockControl state -> Option Bool ->
      Option (Option Bool × Direction × BlockControl state)
  | .root logical, read =>
      if logical = M.halt then none else
      match read with
      | some b0 =>
          some (some b0, Direction.right, .decode1 logical b0)
      | none =>
          match M.transition logical none with
          | none => none
          | some (write, move, target) =>
              let context := blockContext logical none write move target
              some (codeCellBit0 write, Direction.right, .write1 context)
  | .decode1 logical b0, some b1 =>
      some (some b1, Direction.right, .decode2 logical b0 b1)
  | .decode1 _ _, none => none
  | .decode2 logical b0 b1, some b2 =>
      some (some b2, Direction.right, .decode3 logical b0 b1 b2)
  | .decode2 _ _ _, none => none
  | .decode3 logical b0 b1 b2, some b3 =>
      match decodeCodeBits b0 b1 b2 b3 with
      | none => none
      | some read =>
          match M.transition logical (some read) with
          | none => none
          | some (write, move, target) =>
              let context :=
                blockContext logical (some read) write move target
              some (some b3, Direction.left, .back2 context)
  | .decode3 _ _ _ _, none => none
  | .back2 context, read =>
      keepExpected (codeCellBit2 context.read) read Direction.left
        (.back1 context)
  | .back1 context, read =>
      keepExpected (codeCellBit1 context.read) read Direction.left
        (.write0 context)
  | .write0 context, read =>
      writeExpected (codeCellBit0 context.read) read
        (codeCellBit0 context.write) Direction.right (.write1 context)
  | .write1 context, read =>
      writeExpected (codeCellBit1 context.read) read
        (codeCellBit1 context.write) Direction.right (.write2 context)
  | .write2 context, read =>
      writeExpected (codeCellBit2 context.read) read
        (codeCellBit2 context.write) Direction.right (.write3 context)
  | .write3 context, read =>
      if read = codeCellBit3 context.read then
        match context.move with
        | Direction.right =>
            some (codeCellBit3 context.write, Direction.right,
              .root context.target)
        | Direction.left =>
            some (codeCellBit3 context.write, Direction.left,
              .left0 context)
      else none
  | .left0 context, read =>
      keepExpected (codeCellBit2 context.write) read Direction.left
        (.left1 context)
  | .left1 context, read =>
      keepExpected (codeCellBit1 context.write) read Direction.left
        (.left2 context)
  | .left2 context, read =>
      keepExpected (codeCellBit0 context.write) read Direction.left
        (.left3 context)
  | .left3 context, read =>
      some (read, Direction.left, .left4 context)
  | .left4 context, read =>
      some (read, Direction.left, .left5 context)
  | .left5 context, read =>
      some (read, Direction.left, .root context.target)

private def codeBlockMachine [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    TuringMachine Bool (BlockControl state) where
  start := .root M.start
  halt := .root M.halt
  transition := codeBlockTransition M
  statesFinite := BlockControl.finite M.statesFinite

private def blockTapeAtCells
    (leftRev cells : List (Option Bool)) : Tape Bool :=
  match cells with
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

private def physicalizeCodeTape
    (tape : Tape MachineCodeSymbol) : Tape Bool :=
  blockTapeAtCells
    (tape.left.flatMap (fun cell => (codeCellBits cell).reverse))
    (List.append (codeCellBits tape.head)
      (tape.right.flatMap codeCellBits))

private def physicalizeCodeConfig
    (configuration : TuringMachine.Configuration MachineCodeSymbol state) :
    TuringMachine.Configuration Bool (BlockControl state) :=
  { state := .root configuration.state
    tape := physicalizeCodeTape configuration.tape }

private theorem physicalizeCodeTape_read
    (tape : Tape MachineCodeSymbol) :
    Tape.read (physicalizeCodeTape tape) =
      codeCellBit0 (Tape.read tape) := by
  cases tape
  simp [physicalizeCodeTape, blockTapeAtCells, codeCellBits, Tape.read]

private theorem codeCellBits_flatMap_some
    (code : Word MachineCodeSymbol) :
    code.flatMap (fun symbol => codeCellBits (some symbol)) =
      (encodeCodeWordAsInput code).map some := by
  induction code with
  | nil => rfl
  | cons symbol rest ih =>
      change
        List.append (codeCellBits (some symbol))
            (rest.flatMap (fun symbol => codeCellBits (some symbol))) =
          (List.append (encodeCodeSymbolAsInput symbol)
            (encodeCodeWordAsInput rest)).map some
      rw [codeCellBits_some, ih]
      cases symbol <;> rfl

private theorem codeCellBits_flatMap_map_some
    (code : Word MachineCodeSymbol) :
    (code.map some).flatMap codeCellBits =
      (encodeCodeWordAsInput code).map some := by
  induction code with
  | nil => rfl
  | cons symbol rest ih =>
      change
        List.append (codeCellBits (some symbol))
            ((rest.map some).flatMap codeCellBits) =
          (List.append (encodeCodeSymbolAsInput symbol)
            (encodeCodeWordAsInput rest)).map some
      rw [codeCellBits_some, ih]
      cases symbol <;> rfl

private theorem physicalizeCodeTape_input_cons
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    physicalizeCodeTape (Tape.input (first :: rest)) =
      Tape.input (encodeCodeWordAsInput (first :: rest)) := by
  cases first <;>
    simp [physicalizeCodeTape, Tape.input, blockTapeAtCells,
      codeCellBits, codeCellBit0, codeCellBit1, codeCellBit2,
      codeCellBit3, codeCellBits_flatMap_map_some,
      ValidatorBlockSymbol.ofMachineCodeSymbol,
      ValidatorBlockSymbol.firstBit, ValidatorBlockSymbol.secondBit,
      ValidatorBlockSymbol.thirdBit, ValidatorBlockSymbol.fourthBit,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput]

private def codeBlockStepCost
    (read : Option MachineCodeSymbol) (move : Direction) : Nat :=
  match read, move with
  | none, Direction.right => 4
  | none, Direction.left => 10
  | some _, Direction.right => 10
  | some _, Direction.left => 16

private theorem codeBlockMachine_runConfigExact_step
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    (configuration : TuringMachine.Configuration MachineCodeSymbol state)
    (write : Option MachineCodeSymbol) (move : Direction) (target : state)
    (hsource : configuration.state ≠ M.halt)
    (htransition :
      M.transition configuration.state (Tape.read configuration.tape) =
        some (write, move, target)) :
    exists endpoint : TuringMachine.Configuration Bool (BlockControl state),
      (codeBlockMachine M).runConfigExact?
          (codeBlockStepCost (Tape.read configuration.tape) move)
          (physicalizeCodeConfig configuration) = some endpoint ∧
      endpoint.state = .root target ∧
      Tape.Equiv endpoint.tape
        (physicalizeCodeTape
          (Tape.move move (Tape.write write configuration.tape))) := by
  rcases configuration with ⟨logical, ⟨left, head, right⟩⟩
  change logical ≠ M.halt at hsource
  change M.transition logical head = some (write, move, target) at htransition
  cases head with
  | none =>
      cases move with
      | left =>
          cases left with
          | nil =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                keepExpected, writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
                hsource, htransition]
              exact Tape.Equiv.refl _
          | cons previous rest =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                keepExpected, writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
                hsource, htransition]
              exact Tape.Equiv.refl _
      | right =>
          cases right with
          | nil =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveRight,
                hsource, htransition]
              simp [Tape.Equiv, Tape.dropTrailingNone]
          | cons next rest =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveRight,
                hsource, htransition]
              exact Tape.Equiv.refl _
  | some read =>
      cases move with
      | left =>
          cases left with
          | nil =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                keepExpected, writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
                hsource, htransition, decodeCodeBits_components]
              exact Tape.Equiv.refl _
          | cons previous rest =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                keepExpected, writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
                hsource, htransition, decodeCodeBits_components]
              exact Tape.Equiv.refl _
      | right =>
          cases right with
          | nil =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                keepExpected, writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
                hsource, htransition, decodeCodeBits_components]
              simp [Tape.Equiv, Tape.dropTrailingNone]
          | cons next rest =>
              simp [codeBlockStepCost, codeBlockMachine,
                TuringMachine.runConfigExact?, TuringMachine.stepConfig,
                codeBlockTransition, physicalizeCodeConfig,
                physicalizeCodeTape, blockTapeAtCells, codeCellBits,
                codeCellBit0, codeCellBit1, codeCellBit2, codeCellBit3,
                keepExpected, writeExpected, blockContext, Tape.read,
                Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
                hsource, htransition, decodeCodeBits_components]
              exact Tape.Equiv.refl _

private theorem codeBlockStepCost_pos
    (read : Option MachineCodeSymbol) (move : Direction) :
    0 < codeBlockStepCost read move := by
  cases read <;> cases move <;> simp [codeBlockStepCost]

private theorem codeBlockMachine_haltingTransitionsDisabled
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    TuringMachine.HaltingTransitionsDisabled (codeBlockMachine M) := by
  intro cell
  simp [codeBlockMachine, codeBlockTransition]

private theorem codeBlockMachine_computes_step_from_equiv
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    (configuration : TuringMachine.Configuration MachineCodeSymbol state)
    (sourceTape : Tape Bool)
    (write : Option MachineCodeSymbol) (move : Direction) (target : state)
    (hsource : configuration.state ≠ M.halt)
    (htransition :
      M.transition configuration.state (Tape.read configuration.tape) =
        some (write, move, target))
    (htape : Tape.Equiv sourceTape
      (physicalizeCodeTape configuration.tape)) :
    exists endpoint : TuringMachine.Configuration Bool (BlockControl state),
      TuringMachine.Computes (codeBlockMachine M)
        { state := .root configuration.state, tape := sourceTape } endpoint ∧
      endpoint.state = .root target ∧
      Tape.Equiv endpoint.tape
        (physicalizeCodeTape
          (Tape.move move (Tape.write write configuration.tape))) := by
  rcases codeBlockMachine_runConfigExact_step M configuration write move
      target hsource htransition with
    ⟨canonicalEndpoint, hcanonicalRun, hcanonicalState,
      hcanonicalTape⟩
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcanonicalRun (Tape.Equiv.symm htape) with
    ⟨endpoint, hrun, hstate, htapeEndpoint⟩
  refine ⟨endpoint,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun),
    ?_, ?_⟩
  · exact hstate.trans hcanonicalState
  · exact Tape.Equiv.trans (Tape.Equiv.symm htapeEndpoint)
      hcanonicalTape

private theorem codeBlockMachine_haltsFrom_of_logical_haltsFrom
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (configuration : TuringMachine.Configuration MachineCodeSymbol state)
    (sourceTape : Tape Bool)
    (htape : Tape.Equiv sourceTape
      (physicalizeCodeTape configuration.tape))
    (hhalt : TuringMachine.HaltsFrom M configuration) :
    TuringMachine.HaltsFrom (codeBlockMachine M)
      { state := .root configuration.state, tape := sourceTape } := by
  rcases hhalt with ⟨final, hrun, hfinal⟩
  have go :
      forall {source target :
          TuringMachine.Configuration MachineCodeSymbol state},
        TuringMachine.Computes M source target ->
        TuringMachine.Halted M target ->
        forall tape : Tape Bool,
          Tape.Equiv tape (physicalizeCodeTape source.tape) ->
          TuringMachine.HaltsFrom (codeBlockMachine M)
            { state := .root source.state, tape := tape } := by
    intro source target hcomputes
    induction hcomputes with
    | refl source =>
        intro hhalted tape _htape
        exact ⟨{ state := .root source.state, tape := tape },
          TuringMachine.Computes.refl _,
          by simpa [TuringMachine.Halted, codeBlockMachine]
            using congrArg BlockControl.root hhalted⟩
    | @step source next target hstep htail ih =>
        intro hhalted tape htape
        cases hstep with
        | mk htransition =>
            rename_i write move nextState
            have hsource : source.state ≠ M.halt := by
              intro hsource
              have hdisabled := hstop (Tape.read source.tape)
              rw [hsource, hdisabled] at htransition
              cases htransition
            rcases codeBlockMachine_computes_step_from_equiv M source tape
                write move nextState hsource htransition htape with
              ⟨endpoint, hprefix, hendpointState, hendpointTape⟩
            have htailHalt : TuringMachine.HaltsFrom (codeBlockMachine M)
                { state := .root nextState, tape := endpoint.tape } :=
              ih hhalted endpoint.tape hendpointTape
            have hendpointEq :
                endpoint =
                  { state := .root nextState, tape := endpoint.tape } := by
              cases endpoint with
              | mk endpointState endpointTape =>
                  cases hendpointState
                  rfl
            have hprefix' : TuringMachine.Computes (codeBlockMachine M)
                { state := .root source.state, tape := tape }
                { state := .root nextState, tape := endpoint.tape } := by
              rw [← hendpointEq]
              exact hprefix
            exact TuringMachine.halts_from_of_computes_prefix
              hprefix' htailHalt
  exact go hrun hfinal sourceTape htape

private theorem not_haltsFrom_of_not_halted_stepConfig_none
    {M : TuringMachine symbol state}
    {configuration : TuringMachine.Configuration symbol state}
    (hstate : ¬ TuringMachine.Halted M configuration)
    (hstuck : M.stepConfig configuration = none) :
    ¬ TuringMachine.HaltsFrom M configuration := by
  rintro ⟨final, hrun, hfinal⟩
  cases hrun with
  | refl _ =>
      exact hstate hfinal
  | step hstep _ =>
      have hsome := TuringMachine.stepConfig_eq_some_iff_step.mpr hstep
      rw [hstuck] at hsome
      cases hsome

private theorem codeBlockMachine_decode_stuck
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    (configuration : TuringMachine.Configuration MachineCodeSymbol state)
    (read : MachineCodeSymbol)
    (hread : Tape.read configuration.tape = some read)
    (hsource : configuration.state ≠ M.halt)
    (htransition : M.transition configuration.state (some read) = none) :
    exists endpoint : TuringMachine.Configuration Bool (BlockControl state),
      (codeBlockMachine M).runConfigExact? 3
          (physicalizeCodeConfig configuration) = some endpoint ∧
      endpoint.state ≠ (codeBlockMachine M).halt ∧
      (codeBlockMachine M).stepConfig endpoint = none := by
  rcases configuration with ⟨logical, ⟨left, head, right⟩⟩
  change head = some read at hread
  subst head
  change logical ≠ M.halt at hsource
  change M.transition logical (some read) = none at htransition
  simp [codeBlockMachine, TuringMachine.runConfigExact?,
    TuringMachine.stepConfig, codeBlockTransition, physicalizeCodeConfig,
    physicalizeCodeTape, blockTapeAtCells, codeCellBits, codeCellBit0,
    codeCellBit1, codeCellBit2, codeCellBit3, Tape.read, Tape.write,
    Tape.move, Tape.moveRight, hsource, htransition,
    decodeCodeBits_components]

private theorem codeBlockMachine_not_haltsFrom_of_logical_stuck
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    (configuration : TuringMachine.Configuration MachineCodeSymbol state)
    (sourceTape : Tape Bool)
    (htape : Tape.Equiv sourceTape
      (physicalizeCodeTape configuration.tape))
    (hsource : configuration.state ≠ M.halt)
    (htransition :
      M.transition configuration.state (Tape.read configuration.tape) = none) :
    ¬ TuringMachine.HaltsFrom (codeBlockMachine M)
      { state := .root configuration.state, tape := sourceTape } := by
  cases hread : Tape.read configuration.tape with
  | none =>
      have hphysicalRead :
          Tape.read (physicalizeCodeTape configuration.tape) = none := by
        rw [physicalizeCodeTape_read, hread]
        rfl
      have hsourceRead : Tape.read sourceTape = none :=
        (Tape.Equiv.read_eq htape).trans hphysicalRead
      have htransitionNone :
          M.transition configuration.state none = none := by
        simpa [hread] using htransition
      have hstuck :
          (codeBlockMachine M).stepConfig
              { state := .root configuration.state, tape := sourceTape } =
            none := by
        simp [TuringMachine.stepConfig, codeBlockMachine,
          codeBlockTransition, hsource, hsourceRead, htransitionNone]
      apply not_haltsFrom_of_not_halted_stepConfig_none
      · intro hhalted
        change BlockControl.root configuration.state =
          BlockControl.root M.halt at hhalted
        exact hsource (BlockControl.root.inj hhalted)
      · exact hstuck
  | some read =>
      have htransitionRead :
          M.transition configuration.state (some read) = none := by
        simpa [hread] using htransition
      rcases codeBlockMachine_decode_stuck M configuration read hread hsource
          htransitionRead with
        ⟨canonicalEndpoint, hcanonicalRun, hcanonicalNotHalt,
          hcanonicalStuck⟩
      rcases
          TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
            hcanonicalRun (Tape.Equiv.symm htape) with
        ⟨endpoint, hrun, hstate, htapeEndpoint⟩
      have hreadEndpoint : Tape.read endpoint.tape =
          Tape.read canonicalEndpoint.tape :=
        (Tape.Equiv.read_eq htapeEndpoint).symm
      have hcanonicalTransition :
          (codeBlockMachine M).transition canonicalEndpoint.state
              (Tape.read canonicalEndpoint.tape) = none := by
        cases haction :
            (codeBlockMachine M).transition canonicalEndpoint.state
              (Tape.read canonicalEndpoint.tape) with
        | none => rfl
        | some action =>
            simp [TuringMachine.stepConfig, haction] at hcanonicalStuck
      have hstuck : (codeBlockMachine M).stepConfig endpoint = none := by
        have htransitionEndpoint :
            (codeBlockMachine M).transition endpoint.state
                (Tape.read endpoint.tape) = none := by
          rw [hstate, hreadEndpoint]
          exact hcanonicalTransition
        simp [TuringMachine.stepConfig, htransitionEndpoint]
      have hnotHalted :
          ¬ TuringMachine.Halted (codeBlockMachine M) endpoint := by
        intro hhalted
        apply hcanonicalNotHalt
        exact hstate.symm.trans hhalted
      have hnotEndpoint :
          ¬ TuringMachine.HaltsFrom (codeBlockMachine M) endpoint :=
        not_haltsFrom_of_not_halted_stepConfig_none hnotHalted hstuck
      intro hhaltSource
      have hprefix : TuringMachine.Computes (codeBlockMachine M)
          { state := .root configuration.state, tape := sourceTape }
          endpoint :=
        TuringMachine.computesIn_to_computes
          (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)
      have hhaltEndpoint :=
        (TuringMachine.PrefixHalting.haltsFrom_iff_of_computes
          (codeBlockMachine_haltingTransitionsDisabled M) hprefix).mp
          hhaltSource
      exact hnotEndpoint hhaltEndpoint

private theorem codeBlockMachine_logical_haltsFrom_of_haltsFromIn
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    forall (steps : Nat)
      (configuration : TuringMachine.Configuration MachineCodeSymbol state)
      (sourceTape : Tape Bool),
      Tape.Equiv sourceTape (physicalizeCodeTape configuration.tape) ->
      TuringMachine.HaltsFromIn (codeBlockMachine M) steps
        { state := .root configuration.state, tape := sourceTape } ->
      TuringMachine.HaltsFrom M configuration := by
  intro steps
  induction steps using Nat.strongRecOn with
  | ind steps ih =>
      intro configuration sourceTape htape hhalt
      by_cases hhalted : configuration.state = M.halt
      · exact TuringMachine.halts_from_halted hhalted
      cases haction :
          M.transition configuration.state (Tape.read configuration.tape) with
      | none =>
          exact False.elim
            ((codeBlockMachine_not_haltsFrom_of_logical_stuck M
              configuration sourceTape htape hhalted haction)
              (TuringMachine.halts_from_in_to_halts_from hhalt))
      | some action =>
          rcases action with ⟨write, move, target⟩
          rcases codeBlockMachine_runConfigExact_step M configuration write
              move target hhalted haction with
            ⟨canonicalEndpoint, hcanonicalRun, hcanonicalState,
              hcanonicalTape⟩
          rcases
              TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
                hcanonicalRun (Tape.Equiv.symm htape) with
            ⟨endpoint, hrun, hstate, htapeEndpoint⟩
          have hprefix :=
            TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun
          rcases haltsFromIn_suffix_of_computesIn
              (codeBlockMachine_haltingTransitionsDisabled M) hprefix hhalt with
            ⟨remaining, hsteps, hremaining⟩
          have hremainingLt : remaining < steps := by
            have hcost := codeBlockStepCost_pos
              (Tape.read configuration.tape) move
            lia
          have hendpointState : endpoint.state = .root target :=
            hstate.trans hcanonicalState
          have hendpointEq : endpoint =
              { state := .root target, tape := endpoint.tape } := by
            cases endpoint
            cases hendpointState
            rfl
          rw [hendpointEq] at hremaining
          let next : TuringMachine.Configuration MachineCodeSymbol state :=
            { state := target,
              tape := Tape.move move
                (Tape.write write configuration.tape) }
          have hnextTape : Tape.Equiv endpoint.tape
              (physicalizeCodeTape next.tape) :=
            Tape.Equiv.trans (Tape.Equiv.symm htapeEndpoint)
              hcanonicalTape
          have htail : TuringMachine.HaltsFrom M next :=
            ih remaining hremainingLt next endpoint.tape hnextTape
              (by simpa [next] using hremaining)
          exact TuringMachine.halts_from_of_computes_prefix
            (TuringMachine.computes_of_step
              (TuringMachine.Step.mk haction)) htail

private theorem inputTape_equiv_physicalized (code : Word MachineCodeSymbol) :
    Tape.Equiv (Tape.input (encodeCodeWordAsInput code))
      (physicalizeCodeTape (Tape.input code)) := by
  cases code with
  | nil =>
      simp [physicalizeCodeTape, blockTapeAtCells, codeCellBits, codeCellBit0,
        codeCellBit1, codeCellBit2, codeCellBit3, encodeCodeWordAsInput,
        Tape.input, Tape.blank, Tape.Equiv, Tape.dropTrailingNone]
  | cons first rest =>
      rw [physicalizeCodeTape_input_cons]
      exact Tape.Equiv.refl _

def lowerCodeAlphabetMachineDescription [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) : MachineDescription :=
  finiteBoolMachineDescription (codeBlockMachine M)

theorem lowerCodeAlphabetMachineDescription_subroutineReady
    [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state) :
    (lowerCodeAlphabetMachineDescription M).SubroutineReady := by
  exact finiteBoolMachineDescription_subroutineReady (codeBlockMachine M)

theorem lowerCodeAlphabetMachineDescription_haltsOnInput_iff
    [DecidableEq state] (M : TuringMachine MachineCodeSymbol state)
    (hstop : TuringMachine.HaltingTransitionsDisabled M)
    (code : Word MachineCodeSymbol) :
    (lowerCodeAlphabetMachineDescription M).HaltsOnInput
        (encodeCodeWordAsInput code) <-> M.HaltsOnInput code := by
  unfold lowerCodeAlphabetMachineDescription
  rw [finiteBoolMachineDescription_haltsOnInput_iff]
  unfold TuringMachine.HaltsOnInput TuringMachine.initial
  constructor
  · rintro h
    rcases TuringMachine.halts_from_to_halts_from_in h with ⟨steps, hsteps⟩
    exact codeBlockMachine_logical_haltsFrom_of_haltsFromIn M steps _ _
      (inputTape_equiv_physicalized code) hsteps
  · exact codeBlockMachine_haltsFrom_of_logical_haltsFrom M hstop _ _
      (inputTape_equiv_physicalized code)

end CodeAlphabetLowering
end SelfHaltingRecognizer
end Computability
end FoC

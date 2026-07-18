import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.Spec

set_option doc.verso true

/-!
# Four-bit block tables for the exact-code validator

The later validator phases repeatedly scan and temporarily mark complete
four-bit
{name (full := FoC.Computability.MachineCodeSymbol)}`MachineCodeSymbol` cells.
This module packages that physical
bookkeeping locally: a finite sixteen-symbol block alphabet contains the nine
canonical tokens and the seven invalid patterns, and a small table compiler
expands block transitions into ordinary Boolean
{name (full := FoC.Computability.MachineDescription)}`MachineDescription` rows.

The compiler is intentionally scoped to the self-halting validator.  It is not
a promoted general Compiler API: rows may only preserve the final three bits
of a block, so the only supported write is toggling the leading bit.  That is
exactly the operation needed for collision-free markers such as {lit}`0010` ↔
{lit}`1010`, while keeping every logical head position aligned to a four-bit block.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
## Fixed block alphabet
-/

/-- All sixteen Boolean blocks, with canonical code tokens named explicitly. -/
inductive ValidatorBlockSymbol where
  | header
  | transition
  | tick
  | done
  | blank
  | zero
  | one
  | moveLeft
  | moveRight
  | marker001
  | marker010
  | marker011
  | marker100
  | marker101
  | marker110
  | marker111
deriving DecidableEq, Repr

namespace ValidatorBlockSymbol

/-- Four physical bits represented by a block symbol. -/
def bits : ValidatorBlockSymbol -> Word Bool
  | .header => [false, false, false, false]
  | .transition => [false, false, false, true]
  | .tick => [false, false, true, false]
  | .done => [false, false, true, true]
  | .blank => [false, true, false, false]
  | .zero => [false, true, false, true]
  | .one => [false, true, true, false]
  | .moveLeft => [false, true, true, true]
  | .moveRight => [true, false, false, false]
  | .marker001 => [true, false, false, true]
  | .marker010 => [true, false, true, false]
  | .marker011 => [true, false, true, true]
  | .marker100 => [true, true, false, false]
  | .marker101 => [true, true, false, true]
  | .marker110 => [true, true, true, false]
  | .marker111 => [true, true, true, true]

/-- Numeric code used only to allocate disjoint physical action-state blocks. -/
def toNat : ValidatorBlockSymbol -> Nat
  | .header => 0
  | .transition => 1
  | .tick => 2
  | .done => 3
  | .blank => 4
  | .zero => 5
  | .one => 6
  | .moveLeft => 7
  | .moveRight => 8
  | .marker001 => 9
  | .marker010 => 10
  | .marker011 => 11
  | .marker100 => 12
  | .marker101 => 13
  | .marker110 => 14
  | .marker111 => 15

/-- Complete finite enumeration of physical blocks. -/
def all : List ValidatorBlockSymbol :=
  [.header, .transition, .tick, .done, .blank, .zero, .one,
    .moveLeft, .moveRight, .marker001, .marker010, .marker011,
    .marker100, .marker101, .marker110, .marker111]

theorem mem_all (symbol : ValidatorBlockSymbol) : symbol ∈ all := by
  cases symbol <;> simp [all]

/-- Embed a canonical code token into the complete block alphabet. -/
def ofMachineCodeSymbol : MachineCodeSymbol -> ValidatorBlockSymbol
  | .header => .header
  | .transition => .transition
  | .tick => .tick
  | .done => .done
  | .blank => .blank
  | .zero => .zero
  | .one => .one
  | .moveLeft => .moveLeft
  | .moveRight => .moveRight

theorem bits_ofMachineCodeSymbol (symbol : MachineCodeSymbol) :
    bits (ofMachineCodeSymbol symbol) = encodeCodeSymbolAsInput symbol := by
  cases symbol <;> rfl

/-- First physical bit of a complete block. -/
def firstBit : ValidatorBlockSymbol -> Bool
  | .header | .transition | .tick | .done | .blank | .zero | .one |
      .moveLeft => false
  | .moveRight | .marker001 | .marker010 | .marker011 | .marker100 |
      .marker101 | .marker110 | .marker111 => true

/-- Second physical bit of a complete block. -/
def secondBit : ValidatorBlockSymbol -> Bool
  | .header | .transition | .tick | .done | .moveRight | .marker001 |
      .marker010 | .marker011 => false
  | .blank | .zero | .one | .moveLeft | .marker100 | .marker101 |
      .marker110 | .marker111 => true

/-- Third physical bit of a complete block. -/
def thirdBit : ValidatorBlockSymbol -> Bool
  | .header | .transition | .blank | .zero | .moveRight | .marker001 |
      .marker100 | .marker101 => false
  | .tick | .done | .one | .moveLeft | .marker010 | .marker011 |
      .marker110 | .marker111 => true

/-- Fourth physical bit of a complete block. -/
def fourthBit : ValidatorBlockSymbol -> Bool
  | .header | .tick | .blank | .one | .moveRight | .marker010 |
      .marker100 | .marker110 => false
  | .transition | .done | .zero | .moveLeft | .marker001 | .marker011 |
      .marker101 | .marker111 => true

theorem bits_eq_components (symbol : ValidatorBlockSymbol) :
    bits symbol =
      [firstBit symbol, secondBit symbol, thirdBit symbol, fourthBit symbol] := by
  cases symbol <;> rfl

theorem bits_length (symbol : ValidatorBlockSymbol) :
    (bits symbol).length = 4 := by
  cases symbol <;> rfl

/-- The three-bit suffix that marker writes are required to preserve. -/
def tailBits (symbol : ValidatorBlockSymbol) : Bool × Bool × Bool :=
  (secondBit symbol, thirdBit symbol, fourthBit symbol)

theorem tailBits_eq_iff (left right : ValidatorBlockSymbol) :
    tailBits left = tailBits right <->
      secondBit left = secondBit right ∧
        thirdBit left = thirdBit right ∧
          fourthBit left = fourthBit right := by
  simp [tailBits]

theorem eq_of_firstBit_eq_of_tailBits_eq
    {left right : ValidatorBlockSymbol}
    (hfirst : firstBit left = firstBit right)
    (htail : tailBits left = tailBits right) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [firstBit, tailBits, secondBit, thirdBit, fourthBit]

theorem canonical_ne_marker010 (symbol : MachineCodeSymbol) :
    ofMachineCodeSymbol symbol ≠ ValidatorBlockSymbol.marker010 := by
  cases symbol <;> decide

theorem tick_marker_tailBits :
    tailBits .tick = tailBits .marker010 := by
  rfl

theorem transition_marker_tailBits :
    tailBits .transition = tailBits .marker001 := by
  rfl

end ValidatorBlockSymbol

/-- Expand a canonical code word through the local block alphabet. -/
def validatorCanonicalBlocks
    (code : Word MachineCodeSymbol) : Word ValidatorBlockSymbol :=
  code.map ValidatorBlockSymbol.ofMachineCodeSymbol

theorem validatorCanonicalBlocks_append
    (left right : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (List.append left right) =
      List.append
        (validatorCanonicalBlocks left) (validatorCanonicalBlocks right) := by
  unfold validatorCanonicalBlocks
  exact List.map_append

theorem validatorCanonicalBlocks_encodeNatAppend
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    validatorCanonicalBlocks (encodeNatAppend value suffix) =
      List.append
        (validatorCanonicalBlocks (encodeNat value))
        (validatorCanonicalBlocks suffix) := by
  unfold encodeNatAppend
  exact validatorCanonicalBlocks_append _ _

/-- Flatten complete block symbols to their physical Boolean representation. -/
def validatorBlockBits
    (blocks : Word ValidatorBlockSymbol) : Word Bool :=
  blocks.flatMap ValidatorBlockSymbol.bits

theorem validatorBlockBits_canonical
    (code : Word MachineCodeSymbol) :
    validatorBlockBits (validatorCanonicalBlocks code) =
      encodeCodeWordAsInput code := by
  induction code with
  | nil =>
      rfl
  | cons symbol rest ih =>
      change
        List.append
            (ValidatorBlockSymbol.bits
              (ValidatorBlockSymbol.ofMachineCodeSymbol symbol))
            (validatorBlockBits (validatorCanonicalBlocks rest)) =
          List.append (encodeCodeSymbolAsInput symbol)
            (encodeCodeWordAsInput rest)
      rw [ValidatorBlockSymbol.bits_ofMachineCodeSymbol, ih]

/-- Exact physical tape for an aligned block view with the head at the right word. -/
def validatorBlockTape
    (left right : Word ValidatorBlockSymbol) : Tape Bool :=
  tapeAtCells
    (List.append ((validatorBlockBits left).reverse.map some) [none])
    (List.append ((validatorBlockBits right).map some) [none])

/-- Physical cells occupied by one logical block-tape cell. -/
def validatorBlockCellBits : Option ValidatorBlockSymbol ->
    List (Option Bool)
  | none => [none]
  | some symbol => symbol.bits.map some

/-- Expand an arbitrary logical block tape to the exact Boolean tape layout. -/
def validatorPhysicalizeBlockTape
    (tape : Tape ValidatorBlockSymbol) : Tape Bool :=
  tapeAtCells
    (tape.left.flatMap
      (fun cell => (validatorBlockCellBits cell).reverse))
    (List.append (validatorBlockCellBits tape.head)
      (tape.right.flatMap validatorBlockCellBits))

/-!
## Logical block descriptions
-/

/-- One aligned four-bit-block transition. -/
structure ValidatorBlockTransition where
  source : Nat
  read : ValidatorBlockSymbol
  write : ValidatorBlockSymbol
  move : Direction
  target : Nat
deriving DecidableEq

/-- Finite aligned-block table compiled below to a Boolean description. -/
structure ValidatorBlockDescription where
  stateCount : Nat
  start : Nat
  halt : Nat
  transitions : List ValidatorBlockTransition
deriving DecidableEq

namespace ValidatorBlockDescription

def rowMatches (source : Nat) (read : ValidatorBlockSymbol)
    (row : ValidatorBlockTransition) : Bool :=
  row.source == source && row.read == read

def lookup (D : ValidatorBlockDescription)
    (source : Nat) (read : ValidatorBlockSymbol) :
    Option ValidatorBlockTransition :=
  D.transitions.find? (rowMatches source read)

theorem lookup_matches
    {D : ValidatorBlockDescription} {source : Nat}
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup source read = some row) :
    row.source = source ∧ row.read = read := by
  unfold lookup at hlookup
  have hmatches : rowMatches source read row = true :=
    List.find?_some hlookup
  simpa [rowMatches] using hmatches

theorem lookup_mem
    {D : ValidatorBlockDescription} {source : Nat}
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup source read = some row) :
    row ∈ D.transitions := by
  unfold lookup at hlookup
  let predicate := rowMatches source read
  have hmem : forall rows : List ValidatorBlockTransition,
      rows.find? predicate = some row -> row ∈ rows := by
    intro rows
    induction rows with
    | nil => simp
    | cons first rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hmatches : predicate first
        · simp [hmatches] at hfind
          exact List.mem_cons_of_mem first (ih hfind)
        · simp [hmatches] at hfind
          cases hfind
          exact List.mem_cons_self
  exact hmem D.transitions hlookup

/-- Runtime configuration for the aligned logical block semantics. -/
structure Configuration where
  state : Nat
  tape : Tape ValidatorBlockSymbol
deriving DecidableEq

/-- Execute one aligned logical block row. -/
def stepConfig (D : ValidatorBlockDescription)
    (c : Configuration) : Option Configuration :=
  match Tape.read c.tape with
  | none => none
  | some read =>
      match D.lookup c.state read with
      | none => none
      | some row =>
          some
            { state := row.target
              tape := Tape.move row.move (Tape.write (some row.write) c.tape) }

theorem state_lt_of_stepConfig
    {D : ValidatorBlockDescription}
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    {configuration next : Configuration}
    (hstep : D.stepConfig configuration = some next) :
    configuration.state < D.stateCount := by
  unfold stepConfig at hstep
  cases hread : Tape.read configuration.tape with
  | none =>
      simp [hread] at hstep
  | some read =>
      cases hlookup : D.lookup configuration.state read with
      | none =>
          simp [hread, hlookup] at hstep
      | some row =>
          have hmatches := lookup_matches hlookup
          have hbound := hsourceBound row (lookup_mem hlookup)
          simpa [hmatches.1] using hbound

theorem state_ne_halt_of_stepConfig
    {D : ValidatorBlockDescription}
    (hhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    {configuration next : Configuration}
    (hstep : D.stepConfig configuration = some next) :
    configuration.state ≠ D.halt := by
  unfold stepConfig at hstep
  cases hread : Tape.read configuration.tape with
  | none =>
      simp [hread] at hstep
  | some read =>
      cases hlookup : D.lookup configuration.state read with
      | none =>
          simp [hread, hlookup] at hstep
      | some row =>
          have hmatches := lookup_matches hlookup
          have hfree := hhaltFree row (lookup_mem hlookup)
          simpa [hmatches.1] using hfree

/-- Fuel-bounded aligned block execution, stuttering when stuck. -/
def runConfig (D : ValidatorBlockDescription) :
    Nat -> Configuration -> Configuration
  | 0, c => c
  | steps + 1, c =>
      match D.stepConfig c with
      | none => c
      | some next => D.runConfig steps next

theorem runConfig_of_stepConfig_none
    {D : ValidatorBlockDescription} {c : Configuration}
    (hstep : D.stepConfig c = none) :
    forall steps : Nat, D.runConfig steps c = c := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps _ih => simp [runConfig, hstep]

theorem runConfig_add (D : ValidatorBlockDescription)
    (first second : Nat) (c : Configuration) :
    D.runConfig (first + second) c =
      D.runConfig second (D.runConfig first c) := by
  induction first generalizing c with
  | zero => simp [runConfig]
  | succ first ih =>
      rw [Nat.succ_add]
      simp [runConfig]
      cases hstep : D.stepConfig c with
      | none => simp [runConfig_of_stepConfig_none hstep]
      | some next => simp [ih next]

/-- Reflexive-transitive execution currency for logical block proofs. -/
def Reaches (D : ValidatorBlockDescription)
    (source target : Configuration) : Prop :=
  exists steps : Nat, D.runConfig steps source = target

theorem reaches_refl (D : ValidatorBlockDescription)
    (configuration : Configuration) :
    D.Reaches configuration configuration := by
  exact ⟨0, rfl⟩

theorem reaches_of_runConfig
    {D : ValidatorBlockDescription} {source target : Configuration}
    {steps : Nat} (hrun : D.runConfig steps source = target) :
    D.Reaches source target :=
  ⟨steps, hrun⟩

theorem Reaches.trans
    {D : ValidatorBlockDescription} {first second third : Configuration}
    (hfirst : D.Reaches first second)
    (hsecond : D.Reaches second third) :
    D.Reaches first third := by
  rcases hfirst with ⟨firstSteps, hfirst⟩
  rcases hsecond with ⟨secondSteps, hsecond⟩
  refine ⟨firstSteps + secondSteps, ?_⟩
  rw [runConfig_add, hfirst, hsecond]

end ValidatorBlockDescription

/-!
## Exact logical block tapes
-/

/-- Aligned logical tape with its left word in chronological order. -/
def validatorLogicalBlockTape
    (left right : Word ValidatorBlockSymbol) : Tape ValidatorBlockSymbol :=
  let leftRev : List (Option ValidatorBlockSymbol) :=
    List.append (left.reverse.map some) [none]
  match right with
  | [] => { left := leftRev, head := none, right := [] }
  | current :: rest =>
      { left := leftRev, head := some current, right := rest.map some ++ [none] }

theorem validatorLogicalBlockTape_moveRight
    (left rest : Word ValidatorBlockSymbol)
    (read write : ValidatorBlockSymbol) :
    Tape.move Direction.right
        (Tape.write (some write)
          (validatorLogicalBlockTape left (read :: rest))) =
      validatorLogicalBlockTape (List.append left [write]) rest := by
  cases rest <;>
    simp [validatorLogicalBlockTape, Tape.write, Tape.move, Tape.moveRight,
      List.map_reverse]

theorem validatorLogicalBlockTape_moveLeft
    (left rest : Word ValidatorBlockSymbol)
    (previous read write : ValidatorBlockSymbol) :
    Tape.move Direction.left
        (Tape.write (some write)
          (validatorLogicalBlockTape
            (List.append left [previous]) (read :: rest))) =
      validatorLogicalBlockTape left (previous :: write :: rest) := by
  simp [validatorLogicalBlockTape, Tape.write, Tape.move, Tape.moveLeft,
    List.map_reverse]

namespace ValidatorBlockDescription

theorem runConfig_one_right_of_lookup
    {D : ValidatorBlockDescription} {state : Nat}
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup state read = some row)
    (hmove : row.move = Direction.right)
    (left rest : Word ValidatorBlockSymbol) :
    D.runConfig 1
        { state := state
          tape := validatorLogicalBlockTape left (read :: rest) } =
      { state := row.target
        tape := validatorLogicalBlockTape
          (List.append left [row.write]) rest } := by
  have hstep :
      D.stepConfig
          { state := state
            tape := validatorLogicalBlockTape left (read :: rest) } =
        some
          { state := row.target
            tape := validatorLogicalBlockTape
              (List.append left [row.write]) rest } := by
    unfold stepConfig
    rw [show Tape.read (validatorLogicalBlockTape left (read :: rest)) =
      some read by rfl]
    change
      (match D.lookup state read with
        | none => none
        | some found =>
            some (Configuration.mk found.target
              (Tape.move found.move
                (Tape.write (some found.write)
                  (validatorLogicalBlockTape left (read :: rest)))))) =
        some (Configuration.mk row.target
          (validatorLogicalBlockTape
            (List.append left [row.write]) rest))
    rw [hlookup]
    simp only
    rw [hmove, validatorLogicalBlockTape_moveRight]
  unfold runConfig
  rw [hstep]
  rfl

theorem runConfig_one_left_of_lookup
    {D : ValidatorBlockDescription} {state : Nat}
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup state read = some row)
    (hmove : row.move = Direction.left)
    (left rest : Word ValidatorBlockSymbol)
    (previous : ValidatorBlockSymbol) :
    D.runConfig 1
        { state := state
          tape := validatorLogicalBlockTape
            (List.append left [previous]) (read :: rest) } =
      { state := row.target
        tape := validatorLogicalBlockTape left
          (previous :: row.write :: rest) } := by
  have hstep :
      D.stepConfig
          { state := state
            tape := validatorLogicalBlockTape
              (List.append left [previous]) (read :: rest) } =
        some
          { state := row.target
            tape := validatorLogicalBlockTape left
              (previous :: row.write :: rest) } := by
    unfold stepConfig
    rw [show Tape.read
      (validatorLogicalBlockTape
        (List.append left [previous]) (read :: rest)) = some read by rfl]
    change
      (match D.lookup state read with
        | none => none
        | some found =>
            some (Configuration.mk found.target
              (Tape.move found.move
                (Tape.write (some found.write)
                  (validatorLogicalBlockTape
                    (List.append left [previous]) (read :: rest)))))) =
        some (Configuration.mk row.target
          (validatorLogicalBlockTape left
            (previous :: row.write :: rest)))
    rw [hlookup]
    simp only
    rw [hmove, validatorLogicalBlockTape_moveLeft]
  unfold runConfig
  rw [hstep]
  rfl

/-- Scan a homogeneous logical-block run leftward to its boundary. -/
theorem runConfig_scanLeft_replicate
    {D : ValidatorBlockDescription} {state : Nat}
    {symbol boundary : ValidatorBlockSymbol}
    {row : ValidatorBlockTransition}
    (hlookup : D.lookup state symbol = some row)
    (hwrite : row.write = symbol)
    (hmove : row.move = Direction.left)
    (htarget : row.target = state)
    (count : Nat) (before processed : Word ValidatorBlockSymbol) :
    D.runConfig (count + 1)
        { state := state
          tape := validatorLogicalBlockTape
            (List.append
              (List.append before [boundary])
              (List.replicate count symbol))
            (symbol :: processed) } =
      { state := state
        tape := validatorLogicalBlockTape before
          (boundary ::
            List.append (List.replicate (count + 1) symbol) processed) } := by
  change List ValidatorBlockSymbol at before processed
  induction count generalizing processed with
  | zero =>
      have hone := runConfig_one_left_of_lookup
        hlookup hmove before processed boundary
      simpa [hwrite, htarget] using hone
  | succ count ih =>
      rw [show count + 1 + 1 = 1 + (count + 1) by lia]
      rw [runConfig_add]
      have hone := runConfig_one_left_of_lookup
        hlookup hmove
        (List.append (List.append before [boundary])
          (List.replicate count symbol))
        processed symbol
      have hleft :
          (List.append (List.append before [boundary])
              (List.replicate (count + 1) symbol) :
            Word ValidatorBlockSymbol) =
            (List.append
                (List.append (List.append before [boundary])
                  (List.replicate count symbol))
                [symbol] : Word ValidatorBlockSymbol) := by
        change
          List.append (List.append before [boundary])
              (List.replicate (count + 1) symbol) =
            List.append
              (List.append (List.append before [boundary])
                (List.replicate count symbol))
              [symbol]
        rw [List.replicate_succ']
        exact (List.append_assoc (List.append before [boundary])
          (List.replicate count symbol) [symbol]).symm
      rw [hleft]
      rw [hone]
      have htail := ih (symbol :: processed)
      rw [show 1 + (count + 1) = (count + 1) + 1 by lia]
      simpa [hwrite, htarget, List.replicate_succ', List.append_assoc]
        using htail

/-- Scan a homogeneous logical-block run rightward to its boundary. -/
theorem runConfig_scanRight_replicate
    {D : ValidatorBlockDescription} {state : Nat}
    {symbol boundary : ValidatorBlockSymbol}
    {row : ValidatorBlockTransition}
    (hlookup : D.lookup state symbol = some row)
    (hwrite : row.write = symbol)
    (hmove : row.move = Direction.right)
    (htarget : row.target = state)
    (count : Nat) (processed after : Word ValidatorBlockSymbol) :
    D.runConfig (count + 1)
        { state := state
          tape := validatorLogicalBlockTape processed
            (symbol ::
              List.append (List.replicate count symbol) (boundary :: after)) } =
      { state := state
        tape := validatorLogicalBlockTape
          (List.append processed (List.replicate (count + 1) symbol))
          (boundary :: after) } := by
  change List ValidatorBlockSymbol at processed after
  induction count generalizing processed with
  | zero =>
      have hone := runConfig_one_right_of_lookup
        hlookup hmove processed (boundary :: after)
      simpa [hwrite, htarget] using hone
  | succ count ih =>
      rw [show count + 1 + 1 = 1 + (count + 1) by lia]
      rw [runConfig_add]
      rw [show List.replicate (count + 1) symbol =
        symbol :: List.replicate count symbol by rfl]
      have hrest :
          (List.append (symbol :: List.replicate count symbol)
              (boundary :: after) : Word ValidatorBlockSymbol) =
            (symbol ::
              List.append (List.replicate count symbol) (boundary :: after) :
              Word ValidatorBlockSymbol) := by
        rfl
      rw [hrest]
      have hone := runConfig_one_right_of_lookup
        hlookup hmove processed
          (symbol ::
            List.append (List.replicate count symbol) (boundary :: after))
      rw [hone]
      have htail := ih (List.append processed [symbol])
      rw [show 1 + (count + 1) = (count + 1) + 1 by lia]
      rw [show List.replicate ((count + 1) + 1) symbol =
        symbol :: List.replicate (count + 1) symbol by rfl]
      simpa [hwrite, htarget, List.append_assoc] using htail

/-- Rewrite a homogeneous logical-block run while scanning rightward. -/
theorem runConfig_rewriteRight_replicate
    {D : ValidatorBlockDescription} {state : Nat}
    {read write boundary : ValidatorBlockSymbol}
    {row : ValidatorBlockTransition}
    (hlookup : D.lookup state read = some row)
    (hwrite : row.write = write)
    (hmove : row.move = Direction.right)
    (htarget : row.target = state)
    (count : Nat) (processed after : Word ValidatorBlockSymbol) :
    D.runConfig (count + 1)
        { state := state
          tape := validatorLogicalBlockTape processed
            (read ::
              List.append (List.replicate count read) (boundary :: after)) } =
      { state := state
        tape := validatorLogicalBlockTape
          (List.append processed (List.replicate (count + 1) write))
          (boundary :: after) } := by
  change List ValidatorBlockSymbol at processed after
  induction count generalizing processed with
  | zero =>
      have hone := runConfig_one_right_of_lookup
        hlookup hmove processed (boundary :: after)
      simpa [hwrite, htarget] using hone
  | succ count ih =>
      rw [show count + 1 + 1 = 1 + (count + 1) by lia]
      rw [runConfig_add]
      rw [show List.replicate (count + 1) read =
        read :: List.replicate count read by rfl]
      have hrest :
          (List.append (read :: List.replicate count read)
              (boundary :: after) : Word ValidatorBlockSymbol) =
            (read ::
              List.append (List.replicate count read) (boundary :: after) :
              Word ValidatorBlockSymbol) := by
        rfl
      rw [hrest]
      have hone := runConfig_one_right_of_lookup
        hlookup hmove processed
          (read ::
            List.append (List.replicate count read) (boundary :: after))
      rw [hone]
      have htail := ih (List.append processed [write])
      rw [show 1 + (count + 1) = (count + 1) + 1 by lia]
      rw [show List.replicate ((count + 1) + 1) write =
        write :: List.replicate (count + 1) write by rfl]
      simpa [hwrite, htarget, List.append_assoc] using htail

/-!
## Generic logical reachability combinators

These helpers keep construction-specific run files in the aligned-block
currency without repeating the same one-step and heterogeneous-scan proofs.
-/

/-- Compact configuration notation for any aligned-block description. -/
def blockConfiguration
    (state : Nat)
    (left right : Word ValidatorBlockSymbol) :
    ValidatorBlockDescription.Configuration :=
  { state := state
    tape := validatorLogicalBlockTape left right }

/-- Lift one right-moving lookup row to logical reachability. -/
theorem reaches_one_right
    {D : ValidatorBlockDescription}
    {state target : Nat} {read write : ValidatorBlockSymbol}
    (hlookup :
      D.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.right
            target := target })
    (left rest : Word ValidatorBlockSymbol) :
    D.Reaches
        (blockConfiguration state left (read :: rest))
        (blockConfiguration target (List.append left [write]) rest) := by
  apply ValidatorBlockDescription.reaches_of_runConfig
  exact ValidatorBlockDescription.runConfig_one_right_of_lookup
    hlookup rfl left rest

/-- Lift one left-moving lookup row to logical reachability. -/
theorem reaches_one_left
    {D : ValidatorBlockDescription}
    {state target : Nat} {read write : ValidatorBlockSymbol}
    (hlookup :
      D.lookup state read =
        some
          { source := state
            read := read
            write := write
            move := Direction.left
            target := target })
    (left rest : Word ValidatorBlockSymbol)
    (previous : ValidatorBlockSymbol) :
    D.Reaches
        (blockConfiguration state
          (List.append left [previous]) (read :: rest))
        (blockConfiguration target left (previous :: write :: rest)) := by
  apply ValidatorBlockDescription.reaches_of_runConfig
  exact ValidatorBlockDescription.runConfig_one_left_of_lookup
    hlookup rfl left rest previous

/-- Scan a heterogeneous right word while preserving every logical symbol. -/
theorem reaches_scan_right_list
    {D : ValidatorBlockDescription} {state : Nat}
    (symbols : List ValidatorBlockSymbol)
    (hlookup : forall symbol : ValidatorBlockSymbol,
      symbol ∈ symbols ->
        D.lookup state symbol =
          some
            { source := state
              read := symbol
              write := symbol
              move := Direction.right
              target := state })
    (left rest : Word ValidatorBlockSymbol) :
    D.Reaches
        (blockConfiguration state left (List.append symbols rest))
        (blockConfiguration state (List.append left symbols) rest) := by
  induction symbols generalizing left with
  | nil =>
      simpa [blockConfiguration] using
        ValidatorBlockDescription.reaches_refl D
          (blockConfiguration state left rest)
  | cons first tail ih =>
      have hfirst := reaches_one_right
        (hlookup first List.mem_cons_self) left
        (List.append tail rest)
      have htail := ih
        (fun symbol hsymbol =>
          hlookup symbol (List.mem_cons_of_mem first hsymbol))
        (List.append left [first])
      simpa [blockConfiguration, List.append_assoc] using hfirst.trans htail

/-- Cross one left-moving entry row and an encountered heterogeneous word.
The encountered word is supplied in head-first order and therefore appears
reversed in the physical left context. -/
theorem reaches_cross_scan_left_list
    {D : ValidatorBlockDescription} {entry scan : Nat}
    {entryRead entryWrite boundary : ValidatorBlockSymbol}
    (encountered : List ValidatorBlockSymbol)
    (hentry :
      D.lookup entry entryRead =
        some
          { source := entry
            read := entryRead
            write := entryWrite
            move := Direction.left
            target := scan })
    (hscan : forall symbol : ValidatorBlockSymbol,
      symbol ∈ encountered ->
        D.lookup scan symbol =
          some
            { source := scan
              read := symbol
              write := symbol
              move := Direction.left
              target := scan })
    (before after : Word ValidatorBlockSymbol) :
    D.Reaches
        (blockConfiguration entry
          (List.append
            (List.append before [boundary]) encountered.reverse)
          (entryRead :: after))
        (blockConfiguration scan before
          (boundary ::
            List.append encountered.reverse (entryWrite :: after))) := by
  induction encountered generalizing entry entryRead entryWrite after with
  | nil =>
      have hrun := reaches_one_left hentry before after boundary
      simpa [blockConfiguration] using hrun
  | cons first rest ih =>
      have hfirst := reaches_one_left hentry
        (List.append (List.append before [boundary]) rest.reverse)
        after first
      have htail := ih
        (entry := scan) (entryRead := first) (entryWrite := first)
        (hentry := hscan first List.mem_cons_self)
        (hscan := fun symbol hsymbol =>
          hscan symbol (List.mem_cons_of_mem first hsymbol))
        (after := entryWrite :: after)
      simpa [blockConfiguration, List.reverse_cons, List.append_assoc] using
        hfirst.trans htail

end ValidatorBlockDescription

/-!
## Physical table compiler

Each logical state owns a 127-state physical block.  Offsets 0--14 form the
four-bit decoder.  The remaining offsets provide seven contiguous action
states for each of the sixteen decoded blocks; phase six is the optional
boundary bounce.  A logical right move finishes at the first bit of the next
block; a logical left move backs up eight physical cells to the first bit of
the preceding block.  At a blank left boundary, the bounce returns to that
single blank cell instead.
-/

def validatorBlockStateWidth : Nat := 127

def validatorBlockRootState (logical : Nat) : Nat :=
  logical * validatorBlockStateWidth

def validatorBlockBoolCode (bit : Bool) : Nat :=
  if bit then 1 else 0

def validatorBlockDecode1State (logical : Nat) (first : Bool) : Nat :=
  validatorBlockRootState logical + 1 + validatorBlockBoolCode first

def validatorBlockDecode2State
    (logical : Nat) (first second : Bool) : Nat :=
  validatorBlockRootState logical + 3 +
    2 * validatorBlockBoolCode first + validatorBlockBoolCode second

def validatorBlockDecode3State
    (logical : Nat) (first second third : Bool) : Nat :=
  validatorBlockRootState logical + 7 +
    4 * validatorBlockBoolCode first +
      2 * validatorBlockBoolCode second + validatorBlockBoolCode third

/-- Physical decoder leaf reached after reading the first three block bits. -/
def validatorBlockLeafState
    (logical : Nat) (read : ValidatorBlockSymbol) : Nat :=
  validatorBlockDecode3State logical
    read.firstBit read.secondBit read.thirdBit

def validatorBlockActionState
    (logical : Nat) (symbol : ValidatorBlockSymbol) (phase : Nat) : Nat :=
  validatorBlockRootState logical + 15 + 7 * symbol.toNat + phase

def validatorBlockBoundaryState
    (logical : Nat) (symbol : ValidatorBlockSymbol) : Nat :=
  validatorBlockActionState logical symbol 6

def validatorPhysicalRow
    (source : Nat) (read write : Bool)
    (move : Direction) (target : Nat) : TransitionDescription where
  source := source
  read := some read
  write := some write
  move := move
  target := target

def validatorKeepPhysicalRow
    (source : Nat) (read : Bool)
    (move : Direction) (target : Nat) : TransitionDescription :=
  validatorPhysicalRow source read read move target

def validatorKeepEitherRows
    (source : Nat) (move : Direction) (target : Nat) :
    List TransitionDescription :=
  [validatorKeepPhysicalRow source false move target,
    validatorKeepPhysicalRow source true move target]


end SelfHaltingRecognizer
end Computability
end FoC

import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockSimulation

set_option doc.verso true

/-!
# Four-bit block compiler inversion support

This module isolates the nonhalting argument for a decoded block whose leaf
transition is absent.  Keeping it outside the compiler implementation preserves
the repository's per-file size ceiling.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open MachineDescription
open DovetailInitialLayoutInitializer

/-- A missing generated leaf row prevents the physical machine from halting. -/
theorem validatorBlockPhysical_ne_halt_of_leaf_stuck
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    (hhaltFree : M.HaltTransitionFree)
    {logical : Nat} (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    (left right : List (Option ValidatorBlockSymbol))
    (read : ValidatorBlockSymbol)
    (hleafNone :
      M.lookupTransition (validatorBlockLeafState logical read)
          (some read.fourthBit) = none)
    (hleafNotHalt : validatorBlockLeafState logical read ≠ M.halt) :
    forall n : Nat,
      (M.runConfig n
        { state := validatorBlockRootState logical
          tape := validatorPhysicalizeBlockTape
            { left := left, head := some read, right := right } }).state ≠
        M.halt := by
  let source : MachineDescription.Configuration :=
    { state := validatorBlockRootState logical
      tape := validatorPhysicalizeBlockTape
        { left := left, head := some read, right := right } }
  let leafTape :=
    Tape.move Direction.right
      (Tape.move Direction.right
        (Tape.move Direction.right
          (validatorPhysicalizeBlockTape
            { left := left, head := some read, right := right })))
  let stuck : MachineDescription.Configuration :=
    { state := validatorBlockLeafState logical read, tape := leafTape }
  have hprefix : M.runConfig 3 source = stuck := by
    simpa [source, stuck, leafTape, validatorBlockLeafState] using
      runConfig_decodeValidatorBlock
        hsubset hdet hlogical hnotHalt left right read
  have hread : Tape.read leafTape = some read.fourthBit := by
    simp [leafTape, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveRight, tapeAtCells]
  have hstep : M.stepConfig stuck = none := by
    simp [stuck, MachineDescription.stepConfig, hread, hleafNone]
  change forall n : Nat, (M.runConfig n source).state ≠ M.halt
  intro n
  by_cases hle : 3 ≤ n
  · intro hhalt
    let remaining := n - 3
    have hn : n = 3 + remaining := by lia
    have hrun : M.runConfig n source = M.runConfig remaining stuck := by
      rw [hn, MachineDescription.runConfig_add, hprefix]
    have hstay := MachineDescription.runConfig_of_stepConfig_none
      hstep remaining
    have hstate : stuck.state = M.halt := by
      have hstateEq : (M.runConfig n source).state = stuck.state := by
        rw [hrun, hstay]
      exact hstateEq ▸ hhalt
    exact hleafNotHalt hstate

  · intro hhalt
    let remaining := 3 - n
    have hthree : 3 = n + remaining := by lia
    have hrunHalt : M.runConfig n source =
        { state := M.halt, tape := (M.runConfig n source).tape } := by
      cases hcfg : M.runConfig n source with
      | mk state tape =>
          simp [hcfg] at hhalt ⊢
          exact hhalt
    have hstay :
        M.runConfig remaining (M.runConfig n source) =
          M.runConfig n source := by
      rw [hrunHalt]
      exact MachineDescription.runConfig_halt hhaltFree
        (M.runConfig n source).tape remaining
    have hstate : stuck.state = M.halt := by
      have hstuckEq : stuck = M.runConfig n source := by
        rw [← hprefix, hthree, MachineDescription.runConfig_add, hstay]
      rw [hstuckEq]
      exact hhalt
    exact hleafNotHalt hstate

/-- A logical path to a missing leaf row prevents the generated machine from
halting from the physicalized logical source. -/
theorem validatorBlockPhysical_ne_halt_of_logical_leaf_stuck
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    (hMhaltFree : M.HaltTransitionFree)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hDhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {source : ValidatorBlockDescription.Configuration}
    {logical : Nat}
    (left right : List (Option ValidatorBlockSymbol))
    (read : ValidatorBlockSymbol)
    (hreaches : D.Reaches source
      { state := logical
        tape := { left := left, head := some read, right := right } })
    (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    (hleafNone :
      M.lookupTransition (validatorBlockLeafState logical read)
          (some read.fourthBit) = none)
    (hleafNotHalt : validatorBlockLeafState logical read ≠ M.halt) :
    forall n : Nat,
      (M.runConfig n (validatorPhysicalBlockConfiguration source)).state ≠
        M.halt := by
  have hphysical := validatorBlockPhysicalReaches_of_logicalReaches
    hsubset hdet hsourceBound hDhaltFree htailCompatible hreaches
  rcases hphysical with ⟨steps, hrun⟩
  intro n
  apply CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_ne_halt_region
    (n := n) hMhaltFree hrun
  intro remaining
  exact validatorBlockPhysical_ne_halt_of_leaf_stuck
    hsubset hdet hMhaltFree hlogical hnotHalt left right read
    hleafNone hleafNotHalt remaining

/-- Word-oriented wrapper for a stuck aligned logical block. -/
theorem validatorBlockPhysical_ne_halt_of_logicalTape_leaf_stuck
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    (hMhaltFree : M.HaltTransitionFree)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hDhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {source : ValidatorBlockDescription.Configuration}
    {logical : Nat}
    (left right : Languages.Word ValidatorBlockSymbol)
    (read : ValidatorBlockSymbol)
    (hreaches : D.Reaches source
      { state := logical
        tape := validatorLogicalBlockTape left (read :: right) })
    (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    (hleafNone :
      M.lookupTransition (validatorBlockLeafState logical read)
          (some read.fourthBit) = none)
    (hleafNotHalt : validatorBlockLeafState logical read ≠ M.halt) :
    forall n : Nat,
      (M.runConfig n (validatorPhysicalBlockConfiguration source)).state ≠
        M.halt := by
  apply validatorBlockPhysical_ne_halt_of_logical_leaf_stuck
    hsubset hdet hMhaltFree hsourceBound hDhaltFree htailCompatible
    (left.reverse.map some ++ [none])
    (right.map some ++ [none]) read
  · simpa [validatorLogicalBlockTape] using hreaches
  · exact hlogical
  · exact hnotHalt
  · exact hleafNone
  · exact hleafNotHalt

/-- A complete aligned-block witness that a logical source reaches a generated
Boolean leaf with no outgoing row. -/
structure ValidatorBlockLeafStuckWitness
    (D : ValidatorBlockDescription) (M : MachineDescription)
    (source : ValidatorBlockDescription.Configuration) where
  logical : Nat
  left : Languages.Word ValidatorBlockSymbol
  right : Languages.Word ValidatorBlockSymbol
  read : ValidatorBlockSymbol
  reaches : D.Reaches source
    { state := logical
      tape := validatorLogicalBlockTape left (read :: right) }
  logical_lt : logical < D.stateCount
  logical_ne_halt : logical ≠ D.halt
  leaf_none :
    M.lookupTransition (validatorBlockLeafState logical read)
        (some read.fourthBit) = none
  leaf_ne_halt : validatorBlockLeafState logical read ≠ M.halt

/-- Pull a missing-leaf witness backward across a logical execution prefix. -/
def ValidatorBlockLeafStuckWitness.prepend
    {D : ValidatorBlockDescription} {M : MachineDescription}
    {earlier later : ValidatorBlockDescription.Configuration}
    (hprefix : D.Reaches earlier later)
    (witness : ValidatorBlockLeafStuckWitness D M later) :
    ValidatorBlockLeafStuckWitness D M earlier where
  logical := witness.logical
  left := witness.left
  right := witness.right
  read := witness.read
  reaches := hprefix.trans witness.reaches
  logical_lt := witness.logical_lt
  logical_ne_halt := witness.logical_ne_halt
  leaf_none := witness.leaf_none
  leaf_ne_halt := witness.leaf_ne_halt

/-- A logical execution ending at a block root whose tape head is blank. -/
structure ValidatorBlockRootBlankStuckWitness
    (D : ValidatorBlockDescription) (M : MachineDescription)
    (source : ValidatorBlockDescription.Configuration) where
  logical : Nat
  left : Languages.Word ValidatorBlockSymbol
  reaches : D.Reaches source
    { state := logical
      tape := validatorLogicalBlockTape left [] }
  logical_lt : logical < D.stateCount
  logical_ne_halt : logical ≠ D.halt
  root_none :
    M.lookupTransition (validatorBlockRootState logical) none = none
  root_ne_halt : validatorBlockRootState logical ≠ M.halt

/-- Pull a blank-root witness backward across a logical execution prefix. -/
def ValidatorBlockRootBlankStuckWitness.prepend
    {D : ValidatorBlockDescription} {M : MachineDescription}
    {earlier later : ValidatorBlockDescription.Configuration}
    (hprefix : D.Reaches earlier later)
    (witness : ValidatorBlockRootBlankStuckWitness D M later) :
    ValidatorBlockRootBlankStuckWitness D M earlier where
  logical := witness.logical
  left := witness.left
  reaches := hprefix.trans witness.reaches
  logical_lt := witness.logical_lt
  logical_ne_halt := witness.logical_ne_halt
  root_none := witness.root_none
  root_ne_halt := witness.root_ne_halt

/-- Either supported compiler-level stuck shape reached by the validator block
machines. -/
inductive ValidatorBlockStuckWitness
    (D : ValidatorBlockDescription) (M : MachineDescription)
    (source : ValidatorBlockDescription.Configuration) where
  | leaf : ValidatorBlockLeafStuckWitness D M source ->
      ValidatorBlockStuckWitness D M source
  | rootBlank : ValidatorBlockRootBlankStuckWitness D M source ->
      ValidatorBlockStuckWitness D M source

/-- Pull either compiler-level stuck shape backward across a logical prefix. -/
def ValidatorBlockStuckWitness.prepend
    {D : ValidatorBlockDescription} {M : MachineDescription}
    {earlier later : ValidatorBlockDescription.Configuration}
    (hprefix : D.Reaches earlier later) :
    ValidatorBlockStuckWitness D M later ->
      ValidatorBlockStuckWitness D M earlier
  | .leaf witness => .leaf (witness.prepend hprefix)
  | .rootBlank witness => .rootBlank (witness.prepend hprefix)

/-- Consume a complete missing-leaf witness at the physical compiler boundary. -/
theorem validatorBlockPhysical_ne_halt_of_leafStuckWitness
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    (hMhaltFree : M.HaltTransitionFree)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hDhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {source : ValidatorBlockDescription.Configuration}
    (witness : ValidatorBlockLeafStuckWitness D M source) :
    forall n : Nat,
      (M.runConfig n (validatorPhysicalBlockConfiguration source)).state ≠
        M.halt := by
  exact validatorBlockPhysical_ne_halt_of_logicalTape_leaf_stuck
    hsubset hdet hMhaltFree hsourceBound hDhaltFree htailCompatible
    witness.left witness.right witness.read witness.reaches
    witness.logical_lt witness.logical_ne_halt witness.leaf_none
    witness.leaf_ne_halt

/-- Consume a blank-root witness at the physical compiler boundary. -/
theorem validatorBlockPhysical_ne_halt_of_rootBlankStuckWitness
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    (hMhaltFree : M.HaltTransitionFree)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hDhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {source : ValidatorBlockDescription.Configuration}
    (witness : ValidatorBlockRootBlankStuckWitness D M source) :
    forall n : Nat,
      (M.runConfig n (validatorPhysicalBlockConfiguration source)).state ≠
        M.halt := by
  have hphysical := validatorBlockPhysicalReaches_of_logicalReaches
    hsubset hdet hsourceBound hDhaltFree htailCompatible witness.reaches
  rcases hphysical with ⟨steps, hrun⟩
  let stuck := validatorPhysicalBlockConfiguration
    { state := witness.logical
      tape := validatorLogicalBlockTape witness.left [] }
  have hread : Tape.read stuck.tape = none := by
    simp [stuck, validatorPhysicalBlockConfiguration,
      validatorPhysicalizeBlockTape_logical, validatorBlockTape,
      validatorBlockBits, Tape.read, tapeAtCells]
  have hlookup : M.lookupTransition stuck.state none = none := by
    simpa [stuck, validatorPhysicalBlockConfiguration] using
      witness.root_none
  have hstep : M.stepConfig stuck = none := by
    simp [MachineDescription.stepConfig, hread, hlookup]
  have hstate : stuck.state ≠ M.halt := by
    simpa [stuck, validatorPhysicalBlockConfiguration] using
      witness.root_ne_halt
  intro n
  apply CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
    (n := n) hMhaltFree
  · simpa [stuck] using hrun
  · exact hstep
  · exact hstate

/-- Consume either supported compiler-level stuck witness. -/
theorem validatorBlockPhysical_ne_halt_of_stuckWitness
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    (hMhaltFree : M.HaltTransitionFree)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hDhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {source : ValidatorBlockDescription.Configuration}
    (witness : ValidatorBlockStuckWitness D M source) :
    forall n : Nat,
      (M.runConfig n (validatorPhysicalBlockConfiguration source)).state ≠
        M.halt := by
  cases witness with
  | leaf witness =>
      exact validatorBlockPhysical_ne_halt_of_leafStuckWitness
        hsubset hdet hMhaltFree hsourceBound hDhaltFree htailCompatible
        witness
  | rootBlank witness =>
      exact validatorBlockPhysical_ne_halt_of_rootBlankStuckWitness
        hsubset hdet hMhaltFree hsourceBound hDhaltFree htailCompatible
        witness

end SelfHaltingRecognizer
end Computability
end FoC

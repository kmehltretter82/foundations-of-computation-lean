import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine.Basic
set_option doc.verso true
/-! # Generated block compiler and exact physical simulation -/
namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
private def validatorBlockDecoderRows (logical : Nat) :
    List TransitionDescription :=
  [ validatorKeepPhysicalRow (validatorBlockRootState logical) false
      Direction.right (validatorBlockDecode1State logical false)
  , validatorKeepPhysicalRow (validatorBlockRootState logical) true
      Direction.right (validatorBlockDecode1State logical true)
  , validatorKeepPhysicalRow (validatorBlockDecode1State logical false) false
      Direction.right (validatorBlockDecode2State logical false false)
  , validatorKeepPhysicalRow (validatorBlockDecode1State logical false) true
      Direction.right (validatorBlockDecode2State logical false true)
  , validatorKeepPhysicalRow (validatorBlockDecode1State logical true) false
      Direction.right (validatorBlockDecode2State logical true false)
  , validatorKeepPhysicalRow (validatorBlockDecode1State logical true) true
      Direction.right (validatorBlockDecode2State logical true true)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical false false) false Direction.right
      (validatorBlockDecode3State logical false false false)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical false false) true Direction.right
      (validatorBlockDecode3State logical false false true)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical false true) false Direction.right
      (validatorBlockDecode3State logical false true false)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical false true) true Direction.right
      (validatorBlockDecode3State logical false true true)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical true false) false Direction.right
      (validatorBlockDecode3State logical true false false)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical true false) true Direction.right
      (validatorBlockDecode3State logical true false true)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical true true) false Direction.right
      (validatorBlockDecode3State logical true true false)
  , validatorKeepPhysicalRow
      (validatorBlockDecode2State logical true true) true Direction.right
      (validatorBlockDecode3State logical true true true)
  ]

private def validatorBlockRightFlipRows
    (logical : Nat) (read write : ValidatorBlockSymbol)
    (target : Nat) : List TransitionDescription :=
  let a := validatorBlockActionState logical read
  [ validatorKeepPhysicalRow (a 0) read.thirdBit Direction.left (a 1)
  , validatorKeepPhysicalRow (a 1) read.secondBit Direction.left (a 2)
  , validatorPhysicalRow (a 2) read.firstBit write.firstBit
      Direction.right (a 3)
  , validatorKeepPhysicalRow (a 3) read.secondBit Direction.right (a 4)
  , validatorKeepPhysicalRow (a 4) read.thirdBit Direction.right (a 5)
  , validatorKeepPhysicalRow (a 5) read.fourthBit Direction.right
      (validatorBlockRootState target)
  ]

private def validatorBlockLeftRows
    (logical : Nat) (read write : ValidatorBlockSymbol)
    (target : Nat) : List TransitionDescription :=
  let a := validatorBlockActionState logical read
  [ validatorKeepPhysicalRow (a 0) read.thirdBit Direction.left (a 1)
  , validatorKeepPhysicalRow (a 1) read.secondBit Direction.left (a 2)
  , validatorPhysicalRow (a 2) read.firstBit write.firstBit
      Direction.left (a 3)
  ] ++
    [ { source := a 3
        read := none
        write := none
        move := Direction.right
        target := validatorBlockBoundaryState logical read } ] ++
    validatorKeepEitherRows (a 3) Direction.left (a 4) ++
    validatorKeepEitherRows (a 4) Direction.left (a 5) ++
    validatorKeepEitherRows (a 5) Direction.left
      (validatorBlockRootState target) ++
    [validatorKeepPhysicalRow
      (validatorBlockBoundaryState logical read) write.firstBit
      Direction.left (validatorBlockRootState target)]

private def validatorBlockLeafRows
    (D : ValidatorBlockDescription) (logical : Nat)
    (read : ValidatorBlockSymbol) : List TransitionDescription :=
  match D.lookup logical read with
  | none => []
  | some row =>
      if _htail : row.read.tailBits = row.write.tailBits then
        if row.move = Direction.right then
          if row.read.firstBit = row.write.firstBit then
            [validatorKeepPhysicalRow
              (validatorBlockDecode3State logical
                read.firstBit read.secondBit read.thirdBit)
              read.fourthBit Direction.right
              (validatorBlockRootState row.target)]
          else
            [validatorKeepPhysicalRow
                (validatorBlockDecode3State logical
                  read.firstBit read.secondBit read.thirdBit)
                read.fourthBit Direction.left
                (validatorBlockActionState logical read 0)]
        else
          [validatorKeepPhysicalRow
              (validatorBlockDecode3State logical
                read.firstBit read.secondBit read.thirdBit)
              read.fourthBit Direction.left
              (validatorBlockActionState logical read 0)]
      else
        []

private def validatorBlockActionRows
    (D : ValidatorBlockDescription) (logical : Nat)
    (read : ValidatorBlockSymbol) : List TransitionDescription :=
  match D.lookup logical read with
  | none => []
  | some row =>
      if _htail : row.read.tailBits = row.write.tailBits then
        if row.move = Direction.right then
          if row.read.firstBit = row.write.firstBit then
            []
          else
            validatorBlockRightFlipRows logical row.read row.write row.target
        else
          validatorBlockLeftRows logical row.read row.write row.target
      else
        []

private def validatorBlockLogicalRows
    (D : ValidatorBlockDescription) (logical : Nat) :
    List TransitionDescription :=
  if logical = D.halt then
    []
  else
    validatorBlockDecoderRows logical ++
      ValidatorBlockSymbol.all.flatMap
        (validatorBlockLeafRows D logical) ++
      ValidatorBlockSymbol.all.flatMap
        (validatorBlockActionRows D logical)

/-- State-local transition chunks retained for efficient checked proofs. -/
def validatorBlockTransitionChunks
    (D : ValidatorBlockDescription) : List (List TransitionDescription) :=
  (List.range D.stateCount).map (validatorBlockLogicalRows D)

/-- Expand an aligned block table into an ordinary Boolean description. -/
def compileValidatorBlockDescription
    (D : ValidatorBlockDescription) : MachineDescription where
  stateCount := D.stateCount * validatorBlockStateWidth
  start := validatorBlockRootState D.start
  halt := validatorBlockRootState D.halt
  transitions := (validatorBlockTransitionChunks D).flatten

@[simp] theorem compileValidatorBlockDescription_start
    (D : ValidatorBlockDescription) :
    (compileValidatorBlockDescription D).start =
      validatorBlockRootState D.start := rfl

@[simp] theorem compileValidatorBlockDescription_halt
    (D : ValidatorBlockDescription) :
    (compileValidatorBlockDescription D).halt =
      validatorBlockRootState D.halt := rfl

@[simp] theorem compileValidatorBlockDescription_stateCount
    (D : ValidatorBlockDescription) :
    (compileValidatorBlockDescription D).stateCount =
      D.stateCount * validatorBlockStateWidth := rfl

/-- Root-state Boolean representation of one logical block configuration. -/
def validatorPhysicalBlockConfiguration
    (configuration : ValidatorBlockDescription.Configuration) :
    MachineDescription.Configuration :=
  { state := validatorBlockRootState configuration.state
    tape := validatorPhysicalizeBlockTape configuration.tape }

/-!
## Exact physical simulation
-/

/-- Reflexive-transitive exact execution used by the local block compiler. -/
def ValidatorBlockPhysicalReaches
    (M : MachineDescription)
    (source target : MachineDescription.Configuration) : Prop :=
  exists steps : Nat, M.runConfig steps source = target

theorem validatorBlockPhysicalReaches_refl
    (M : MachineDescription)
    (configuration : MachineDescription.Configuration) :
    ValidatorBlockPhysicalReaches M configuration configuration := by
  exact ⟨0, rfl⟩

theorem ValidatorBlockPhysicalReaches.trans
    {M : MachineDescription}
    {first second third : MachineDescription.Configuration}
    (hfirst : ValidatorBlockPhysicalReaches M first second)
    (hsecond : ValidatorBlockPhysicalReaches M second third) :
    ValidatorBlockPhysicalReaches M first third := by
  rcases hfirst with ⟨firstSteps, hfirst⟩
  rcases hsecond with ⟨secondSteps, hsecond⟩
  refine ⟨firstSteps + secondSteps, ?_⟩
  rw [MachineDescription.runConfig_add, hfirst, hsecond]

private theorem lookupTransition_eq_some_of_mem_deterministic
    {M : MachineDescription} (hdet : M.Deterministic)
    {row : TransitionDescription} (hrow : row ∈ M.transitions) :
    M.lookupTransition row.source row.read = some row := by
  cases hlookup : M.lookupTransition row.source row.read with
  | none =>
      unfold MachineDescription.lookupTransition at hlookup
      have hmiss := List.find?_eq_none.mp hlookup row hrow
      have hmatches :
          MachineDescription.Matches row.source row.read row = true := by
        simp [MachineDescription.Matches]
      rw [hmatches] at hmiss
      contradiction
  | some found =>
      have hfoundMem : found ∈ M.transitions :=
        MachineDescription.lookupTransition_mem hlookup
      have hfoundMatches :=
        MachineDescription.lookupTransition_matches hlookup
      have haction := hdet row found hrow hfoundMem
        ⟨hfoundMatches.1.symm, hfoundMatches.2.symm⟩
      cases row
      cases found
      simp_all [TransitionDescription.SameAction]

private theorem validatorBlockLogicalRow_mem_compile
    {D : ValidatorBlockDescription} {logical : Nat}
    {row : TransitionDescription}
    (hlogical : logical < D.stateCount)
    (hrow : row ∈ validatorBlockLogicalRows D logical) :
    row ∈ (compileValidatorBlockDescription D).transitions := by
  rw [compileValidatorBlockDescription,
    validatorBlockTransitionChunks, List.mem_flatten]
  refine ⟨validatorBlockLogicalRows D logical, ?_, hrow⟩
  rw [List.mem_map]
  exact ⟨logical, List.mem_range.mpr hlogical, rfl⟩

private theorem validatorBlockDecoderRow_mem_logicalRows
    {D : ValidatorBlockDescription} {logical : Nat}
    (hnotHalt : logical ≠ D.halt)
    {row : TransitionDescription}
    (hrow : row ∈ validatorBlockDecoderRows logical) :
    row ∈ validatorBlockLogicalRows D logical := by
  simp only [validatorBlockLogicalRows, if_neg hnotHalt,
    List.mem_append]
  exact Or.inl (Or.inl hrow)

private theorem validatorBlockDecoderRootRow_mem
    (logical : Nat) (first : Bool) :
    validatorKeepPhysicalRow
        (validatorBlockRootState logical) first Direction.right
        (validatorBlockDecode1State logical first) ∈
      validatorBlockDecoderRows logical := by
  cases first <;> simp [validatorBlockDecoderRows]

private theorem validatorBlockDecoderOneRow_mem
    (logical : Nat) (first second : Bool) :
    validatorKeepPhysicalRow
        (validatorBlockDecode1State logical first) second Direction.right
        (validatorBlockDecode2State logical first second) ∈
      validatorBlockDecoderRows logical := by
  cases first <;> cases second <;> simp [validatorBlockDecoderRows]

private theorem validatorBlockDecoderTwoRow_mem
    (logical : Nat) (first second third : Bool) :
    validatorKeepPhysicalRow
        (validatorBlockDecode2State logical first second) third Direction.right
        (validatorBlockDecode3State logical first second third) ∈
      validatorBlockDecoderRows logical := by
  cases first <;> cases second <;> cases third <;>
    simp [validatorBlockDecoderRows]

private theorem validatorBlockLeafRow_mem_logicalRows
    {D : ValidatorBlockDescription} {logical : Nat}
    (hnotHalt : logical ≠ D.halt)
    (read : ValidatorBlockSymbol) {row : TransitionDescription}
    (hrow : row ∈ validatorBlockLeafRows D logical read) :
    row ∈ validatorBlockLogicalRows D logical := by
  simp only [validatorBlockLogicalRows, if_neg hnotHalt,
    List.mem_append]
  refine Or.inl (Or.inr ?_)
  rw [List.mem_flatMap]
  exact ⟨read, ValidatorBlockSymbol.mem_all read, hrow⟩

private theorem validatorBlockActionRow_mem_logicalRows
    {D : ValidatorBlockDescription} {logical : Nat}
    (hnotHalt : logical ≠ D.halt)
    (read : ValidatorBlockSymbol) {row : TransitionDescription}
    (hrow : row ∈ validatorBlockActionRows D logical read) :
    row ∈ validatorBlockLogicalRows D logical := by
  simp only [validatorBlockLogicalRows, if_neg hnotHalt,
    List.mem_append]
  refine Or.inr ?_
  rw [List.mem_flatMap]
  exact ⟨read, ValidatorBlockSymbol.mem_all read, hrow⟩

private theorem validatorBlockRightFlipRow_mem_logicalRows
    {D : ValidatorBlockDescription} {logical : Nat}
    (hnotHalt : logical ≠ D.halt)
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup logical read = some row)
    (htail : row.read.tailBits = row.write.tailBits)
    (hmove : row.move = Direction.right)
    (hfirst : row.read.firstBit ≠ row.write.firstBit)
    {physicalRow : TransitionDescription}
    (hphysical : physicalRow ∈ validatorBlockRightFlipRows
      logical read row.write row.target) :
    physicalRow ∈ validatorBlockLogicalRows D logical := by
  have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
  have htailRead : read.tailBits = row.write.tailBits := by
    rw [← hreadEq]
    exact htail
  have hfirstRead : read.firstBit ≠ row.write.firstBit := by
    rw [← hreadEq]
    exact hfirst
  apply validatorBlockActionRow_mem_logicalRows hnotHalt read
  simpa [validatorBlockActionRows, hlookup, htail, hmove, hfirst,
    hreadEq, htailRead, hfirstRead] using hphysical

private theorem validatorBlockLeftRow_mem_logicalRows
    {D : ValidatorBlockDescription} {logical : Nat}
    (hnotHalt : logical ≠ D.halt)
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup logical read = some row)
    (htail : row.read.tailBits = row.write.tailBits)
    (hmove : row.move = Direction.left)
    {physicalRow : TransitionDescription}
    (hphysical : physicalRow ∈ validatorBlockLeftRows
      logical read row.write row.target) :
    physicalRow ∈ validatorBlockLogicalRows D logical := by
  have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
  have htailRead : read.tailBits = row.write.tailBits := by
    rw [← hreadEq]
    exact htail
  apply validatorBlockActionRow_mem_logicalRows hnotHalt read
  simpa [validatorBlockActionRows, hlookup, htail, hmove, hreadEq,
    htailRead]
    using hphysical

private theorem runConfig_one_of_validatorBlockLogicalRow
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    {logical : Nat} (hlogical : logical < D.stateCount)
    {row : TransitionDescription}
    (hrow : row ∈ validatorBlockLogicalRows D logical)
    (tape : Tape Bool) (hread : Tape.read tape = row.read) :
    M.runConfig 1 { state := row.source, tape := tape } =
      { state := row.target
        tape := Tape.move row.move (Tape.write row.write tape) } := by
  have hrowCompiled :=
    validatorBlockLogicalRow_mem_compile hlogical hrow
  have hrowAmbient := hsubset row hrowCompiled
  have hlookup :=
    lookupTransition_eq_some_of_mem_deterministic hdet hrowAmbient
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hread, hlookup]

private theorem lookupTransition_of_validatorBlockLogicalRow
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    {logical : Nat} (hlogical : logical < D.stateCount)
    {row : TransitionDescription}
    (hrow : row ∈ validatorBlockLogicalRows D logical) :
    M.lookupTransition row.source row.read = some row := by
  apply lookupTransition_eq_some_of_mem_deterministic hdet
  apply hsubset row
  exact validatorBlockLogicalRow_mem_compile hlogical hrow

private def validatorBlockDecodedTape (tape : Tape Bool) : Tape Bool :=
  Tape.move Direction.right
    (Tape.move Direction.right (Tape.move Direction.right tape))

private def validatorBlockRewrittenFirstTape
    (write : ValidatorBlockSymbol) (tape : Tape Bool) : Tape Bool :=
  Tape.write (some write.firstBit)
    (Tape.move Direction.left
      (Tape.move Direction.left
        (Tape.move Direction.left (validatorBlockDecodedTape tape))))

private def validatorBlockRightResultTape
    (write : ValidatorBlockSymbol) (tape : Tape Bool) : Tape Bool :=
  Tape.move Direction.right
    (Tape.move Direction.right
      (Tape.move Direction.right
        (Tape.move Direction.right
          (validatorBlockRewrittenFirstTape write tape))))

private def validatorBlockLeftResultTape
    (write : ValidatorBlockSymbol) (tape : Tape Bool) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.left
      (Tape.move Direction.left
        (Tape.move Direction.left
          (validatorBlockRewrittenFirstTape write tape))))

private def validatorBlockBoundaryLeftResultTape
    (write : ValidatorBlockSymbol) (tape : Tape Bool) : Tape Bool :=
  Tape.move Direction.left
    (Tape.move Direction.right
      (Tape.move Direction.left
        (validatorBlockRewrittenFirstTape write tape)))

private theorem validatorPhysicalizeBlockTape_write_moveRight
    (left right : List (Option ValidatorBlockSymbol))
    (read write : ValidatorBlockSymbol)
    (htail : read.tailBits = write.tailBits) :
    validatorPhysicalizeBlockTape
        (Tape.move Direction.right
          (Tape.write (some write)
            { left := left, head := some read, right := right })) =
      validatorBlockRightResultTape write
        (validatorPhysicalizeBlockTape
          { left := left, head := some read, right := right }) := by
  rcases (ValidatorBlockSymbol.tailBits_eq_iff read write).mp htail with
    ⟨hsecond, hthird, hfourth⟩
  cases right with
  | nil =>
    simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
      validatorBlockRightResultTape, validatorBlockRewrittenFirstTape,
      validatorBlockDecodedTape,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
      hsecond, hthird, hfourth]
  | cons next rest =>
    cases next <;>
      simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
        validatorBlockRightResultTape, validatorBlockRewrittenFirstTape,
        validatorBlockDecodedTape,
        ValidatorBlockSymbol.bits_eq_components,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
        hsecond, hthird, hfourth]

private theorem validatorBlockRightResultTape_same
    (left right : List (Option ValidatorBlockSymbol))
    (read : ValidatorBlockSymbol) :
    validatorBlockRightResultTape read
        (validatorPhysicalizeBlockTape
          { left := left, head := some read, right := right }) =
      Tape.move Direction.right
        (validatorBlockDecodedTape
          (validatorPhysicalizeBlockTape
            { left := left, head := some read, right := right })) := by
  cases right with
  | nil =>
    simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
      validatorBlockRightResultTape, validatorBlockRewrittenFirstTape,
      validatorBlockDecodedTape,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  | cons next rest =>
    cases next <;>
      simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
        validatorBlockRightResultTape, validatorBlockRewrittenFirstTape,
        validatorBlockDecodedTape,
        ValidatorBlockSymbol.bits_eq_components,
        Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

private theorem validatorPhysicalizeBlockTape_write_moveLeft_some
    (left right : List (Option ValidatorBlockSymbol))
    (previous read write : ValidatorBlockSymbol)
    (htail : read.tailBits = write.tailBits) :
    validatorPhysicalizeBlockTape
        (Tape.move Direction.left
          (Tape.write (some write)
            { left := some previous :: left
              head := some read
              right := right })) =
      validatorBlockLeftResultTape write
        (validatorPhysicalizeBlockTape
          { left := some previous :: left
            head := some read
            right := right }) := by
  rcases (ValidatorBlockSymbol.tailBits_eq_iff read write).mp htail with
    ⟨hsecond, hthird, hfourth⟩
  simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
    validatorBlockLeftResultTape, validatorBlockRewrittenFirstTape,
    validatorBlockDecodedTape,
    ValidatorBlockSymbol.bits_eq_components,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
    hsecond, hthird, hfourth]

private theorem validatorPhysicalizeBlockTape_write_moveLeft_none
    (left right : List (Option ValidatorBlockSymbol))
    (read write : ValidatorBlockSymbol)
    (htail : read.tailBits = write.tailBits) :
    validatorPhysicalizeBlockTape
        (Tape.move Direction.left
          (Tape.write (some write)
            { left := none :: left, head := some read, right := right })) =
      validatorBlockBoundaryLeftResultTape write
        (validatorPhysicalizeBlockTape
          { left := none :: left, head := some read, right := right }) := by
  rcases (ValidatorBlockSymbol.tailBits_eq_iff read write).mp htail with
    ⟨hsecond, hthird, hfourth⟩
  simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
    validatorBlockBoundaryLeftResultTape,
    validatorBlockRewrittenFirstTape, validatorBlockDecodedTape,
    ValidatorBlockSymbol.bits_eq_components,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
    hsecond, hthird, hfourth]

private theorem validatorPhysicalizeBlockTape_write_moveLeft_nil
    (right : List (Option ValidatorBlockSymbol))
    (read write : ValidatorBlockSymbol)
    (htail : read.tailBits = write.tailBits) :
    validatorPhysicalizeBlockTape
        (Tape.move Direction.left
          (Tape.write (some write)
            { left := [], head := some read, right := right })) =
      validatorBlockBoundaryLeftResultTape write
        (validatorPhysicalizeBlockTape
          { left := [], head := some read, right := right }) := by
  rcases (ValidatorBlockSymbol.tailBits_eq_iff read write).mp htail with
    ⟨hsecond, hthird, hfourth⟩
  simp [validatorPhysicalizeBlockTape, validatorBlockCellBits,
    validatorBlockBoundaryLeftResultTape,
    validatorBlockRewrittenFirstTape, validatorBlockDecodedTape,
    ValidatorBlockSymbol.bits_eq_components,
    Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells,
    hsecond, hthird, hfourth]

/-- Three physical decoder steps read the first three aligned block bits. -/
theorem runConfig_decodeValidatorBlock
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall row : TransitionDescription,
      row ∈ (compileValidatorBlockDescription D).transitions ->
        row ∈ M.transitions)
    (hdet : M.Deterministic)
    {logical : Nat} (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    (left right : List (Option ValidatorBlockSymbol))
    (read : ValidatorBlockSymbol) :
    M.runConfig 3
        { state := validatorBlockRootState logical
          tape := validatorPhysicalizeBlockTape
            { left := left, head := some read, right := right } } =
      { state := validatorBlockDecode3State logical
          read.firstBit read.secondBit read.thirdBit
        tape :=
          Tape.move Direction.right
            (Tape.move Direction.right
              (Tape.move Direction.right
                (validatorPhysicalizeBlockTape
                  { left := left, head := some read, right := right }))) } := by
  let tape0 := validatorPhysicalizeBlockTape
    { left := left, head := some read, right := right }
  let tape1 := Tape.move Direction.right tape0
  let tape2 := Tape.move Direction.right tape1
  let tape3 := Tape.move Direction.right tape2
  have hread0 : Tape.read tape0 = some read.firstBit := by
    simp [tape0, validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components, tapeAtCells, Tape.read]
  have hread1 : Tape.read tape1 = some read.secondBit := by
    simp [tape1, tape0, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      tapeAtCells, Tape.read, Tape.move, Tape.moveRight]
  have hread2 : Tape.read tape2 = some read.thirdBit := by
    simp [tape2, tape1, tape0, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      tapeAtCells, Tape.read, Tape.move, Tape.moveRight]
  have hwrite0 : Tape.write (some read.firstBit) tape0 = tape0 := by
    rw [← hread0]
    exact Tape.write_read_eq_self tape0
  have hwrite1 : Tape.write (some read.secondBit) tape1 = tape1 := by
    rw [← hread1]
    exact Tape.write_read_eq_self tape1
  have hwrite2 : Tape.write (some read.thirdBit) tape2 = tape2 := by
    rw [← hread2]
    exact Tape.write_read_eq_self tape2
  have hrow0 :
      validatorKeepPhysicalRow
          (validatorBlockRootState logical) read.firstBit Direction.right
          (validatorBlockDecode1State logical read.firstBit) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockDecoderRow_mem_logicalRows hnotHalt
    exact validatorBlockDecoderRootRow_mem logical read.firstBit
  have hrow1 :
      validatorKeepPhysicalRow
          (validatorBlockDecode1State logical read.firstBit)
          read.secondBit Direction.right
          (validatorBlockDecode2State logical
            read.firstBit read.secondBit) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockDecoderRow_mem_logicalRows hnotHalt
    exact validatorBlockDecoderOneRow_mem logical
      read.firstBit read.secondBit
  have hrow2 :
      validatorKeepPhysicalRow
          (validatorBlockDecode2State logical
            read.firstBit read.secondBit)
          read.thirdBit Direction.right
          (validatorBlockDecode3State logical
            read.firstBit read.secondBit read.thirdBit) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockDecoderRow_mem_logicalRows hnotHalt
    exact validatorBlockDecoderTwoRow_mem logical
      read.firstBit read.secondBit read.thirdBit
  have hstep0 :
      M.runConfig 1
          { state := validatorBlockRootState logical, tape := tape0 } =
        { state := validatorBlockDecode1State logical read.firstBit
          tape := tape1 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical hrow0 tape0 hread0
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite0, tape1] using hrun
  have hstep1 :
      M.runConfig 1
          { state := validatorBlockDecode1State logical read.firstBit
            tape := tape1 } =
        { state := validatorBlockDecode2State logical
            read.firstBit read.secondBit
          tape := tape2 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical hrow1 tape1 hread1
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite1, tape2] using hrun
  have hstep2 :
      M.runConfig 1
          { state := validatorBlockDecode2State logical
              read.firstBit read.secondBit
            tape := tape2 } =
        { state := validatorBlockDecode3State logical
            read.firstBit read.secondBit read.thirdBit
          tape := tape3 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical hrow2 tape2 hread2
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite2, tape3] using hrun
  change M.runConfig 3
      { state := validatorBlockRootState logical, tape := tape0 } =
    { state := validatorBlockDecode3State logical
        read.firstBit read.secondBit read.thirdBit
      tape := tape3 }
  rw [show 3 = 1 + 2 by decide,
    MachineDescription.runConfig_add, hstep0]
  rw [show 2 = 1 + 1 by decide,
    MachineDescription.runConfig_add, hstep1, hstep2]

private theorem runConfig_finishValidatorBlock_right_same
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall physicalRow : TransitionDescription,
      physicalRow ∈ (compileValidatorBlockDescription D).transitions ->
        physicalRow ∈ M.transitions)
    (hdet : M.Deterministic)
    {logical : Nat} (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup logical read = some row)
    (htail : row.read.tailBits = row.write.tailBits)
    (hmove : row.move = Direction.right)
    (hfirst : row.read.firstBit = row.write.firstBit)
    (left right : List (Option ValidatorBlockSymbol)) :
    M.runConfig 1
        { state := validatorBlockDecode3State logical
            read.firstBit read.secondBit read.thirdBit
          tape := validatorBlockDecodedTape
            (validatorPhysicalizeBlockTape
              { left := left, head := some read, right := right }) } =
      { state := validatorBlockRootState row.target
        tape := validatorPhysicalizeBlockTape
          (Tape.move Direction.right
            (Tape.write (some row.write)
              { left := left, head := some read, right := right })) } := by
  have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
  have htailRead : read.tailBits = row.write.tailBits := by
    rw [← hreadEq]
    exact htail
  have hfirstRead : read.firstBit = row.write.firstBit := by
    rw [← hreadEq]
    exact hfirst
  have hwriteEq : read = row.write :=
    ValidatorBlockSymbol.eq_of_firstBit_eq_of_tailBits_eq
      hfirstRead htailRead
  let tape0 := validatorPhysicalizeBlockTape
    { left := left, head := some read, right := right }
  let tape3 := validatorBlockDecodedTape tape0
  have hread3 : Tape.read tape3 = some read.fourthBit := by
    simp [tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveRight, tapeAtCells]
  have hwrite3 : Tape.write (some read.fourthBit) tape3 = tape3 := by
    rw [← hread3]
    exact Tape.write_read_eq_self tape3
  have hleaf :
      validatorKeepPhysicalRow
          (validatorBlockDecode3State logical
            read.firstBit read.secondBit read.thirdBit)
          read.fourthBit Direction.right
          (validatorBlockRootState row.target) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockLeafRow_mem_logicalRows hnotHalt read
    simp [validatorBlockLeafRows, hlookup, htail, hmove, hfirst]
  have hrun := runConfig_one_of_validatorBlockLogicalRow
    hsubset hdet hlogical hleaf tape3 hread3
  have hstep :
      M.runConfig 1
          { state := validatorBlockDecode3State logical
              read.firstBit read.secondBit read.thirdBit
            tape := tape3 } =
        { state := validatorBlockRootState row.target
          tape := Tape.move Direction.right tape3 } := by
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow, hwrite3]
      using hrun
  have hphysical := validatorPhysicalizeBlockTape_write_moveRight
    left right read row.write htailRead
  have hresult := validatorBlockRightResultTape_same left right read
  rw [← hwriteEq] at hphysical
  change M.runConfig 1
      { state := validatorBlockDecode3State logical
          read.firstBit read.secondBit read.thirdBit
        tape := tape3 } = _
  rw [hstep]
  rw [← hwriteEq]
  rw [hphysical, hresult]

private theorem physicallyReaches_finishValidatorBlock_right_flip
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall physicalRow : TransitionDescription,
      physicalRow ∈ (compileValidatorBlockDescription D).transitions ->
        physicalRow ∈ M.transitions)
    (hdet : M.Deterministic)
    {logical : Nat} (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup logical read = some row)
    (htail : row.read.tailBits = row.write.tailBits)
    (hmove : row.move = Direction.right)
    (hfirst : row.read.firstBit ≠ row.write.firstBit)
    (left right : List (Option ValidatorBlockSymbol)) :
    ValidatorBlockPhysicalReaches M
      { state := validatorBlockDecode3State logical
          read.firstBit read.secondBit read.thirdBit
        tape := validatorBlockDecodedTape
          (validatorPhysicalizeBlockTape
            { left := left, head := some read, right := right }) }
      { state := validatorBlockRootState row.target
        tape := validatorPhysicalizeBlockTape
          (Tape.move Direction.right
            (Tape.write (some row.write)
              { left := left, head := some read, right := right })) } := by
  have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
  have htailRead : read.tailBits = row.write.tailBits := by
    rw [← hreadEq]
    exact htail
  have hfirstRead : read.firstBit ≠ row.write.firstBit := by
    rw [← hreadEq]
    exact hfirst
  rcases (ValidatorBlockSymbol.tailBits_eq_iff read row.write).mp
      htailRead with ⟨hsecond, hthird, hfourth⟩
  let tape0 := validatorPhysicalizeBlockTape
    { left := left, head := some read, right := right }
  let tape3 := validatorBlockDecodedTape tape0
  let tape4 := Tape.move Direction.left tape3
  let tape5 := Tape.move Direction.left tape4
  let tape6 := Tape.move Direction.left tape5
  let tape7 := Tape.move Direction.right
    (Tape.write (some row.write.firstBit) tape6)
  let tape8 := Tape.move Direction.right tape7
  let tape9 := Tape.move Direction.right tape8
  let tape10 := Tape.move Direction.right tape9
  have hread3 : Tape.read tape3 = some read.fourthBit := by
    simp [tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveRight, tapeAtCells]
  have hread4 : Tape.read tape4 = some read.thirdBit := by
    simp [tape4, tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  have hread5 : Tape.read tape5 = some read.secondBit := by
    simp [tape5, tape4, tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  have hread6 : Tape.read tape6 = some read.firstBit := by
    simp [tape6, tape5, tape4, tape3, tape0,
      validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  have hread7 : Tape.read tape7 = some read.secondBit := by
    simp [tape7, tape6, tape5, tape4, tape3, tape0,
      validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
      tapeAtCells]
  have hread8 : Tape.read tape8 = some read.thirdBit := by
    simp [tape8, tape7, tape6, tape5, tape4, tape3, tape0,
      validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
      tapeAtCells]
  have hread9 : Tape.read tape9 = some read.fourthBit := by
    simp [tape9, tape8, tape7, tape6, tape5, tape4, tape3, tape0,
      validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
      tapeAtCells]
  have hwrite3 : Tape.write (some read.fourthBit) tape3 = tape3 := by
    rw [← hread3]
    exact Tape.write_read_eq_self tape3
  have hwrite4 : Tape.write (some read.thirdBit) tape4 = tape4 := by
    rw [← hread4]
    exact Tape.write_read_eq_self tape4
  have hwrite5 : Tape.write (some read.secondBit) tape5 = tape5 := by
    rw [← hread5]
    exact Tape.write_read_eq_self tape5
  have hwrite7 : Tape.write (some read.secondBit) tape7 = tape7 := by
    rw [← hread7]
    exact Tape.write_read_eq_self tape7
  have hwrite8 : Tape.write (some read.thirdBit) tape8 = tape8 := by
    rw [← hread8]
    exact Tape.write_read_eq_self tape8
  have hwrite9 : Tape.write (some read.fourthBit) tape9 = tape9 := by
    rw [← hread9]
    exact Tape.write_read_eq_self tape9
  let a := validatorBlockActionState logical read
  have hleaf :
      validatorKeepPhysicalRow
          (validatorBlockDecode3State logical
            read.firstBit read.secondBit read.thirdBit)
          read.fourthBit Direction.left (a 0) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockLeafRow_mem_logicalRows hnotHalt read
    simp [validatorBlockLeafRows, hlookup, htail, hmove, hfirst, a]
  have haction0 :
      validatorKeepPhysicalRow (a 0) read.thirdBit Direction.left (a 1) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockRightFlipRow_mem_logicalRows
      hnotHalt hlookup htail hmove hfirst
    simp [validatorBlockRightFlipRows, a]
  have haction1 :
      validatorKeepPhysicalRow (a 1) read.secondBit Direction.left (a 2) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockRightFlipRow_mem_logicalRows
      hnotHalt hlookup htail hmove hfirst
    simp [validatorBlockRightFlipRows, a]
  have haction2 :
      validatorPhysicalRow (a 2) read.firstBit row.write.firstBit
          Direction.right (a 3) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockRightFlipRow_mem_logicalRows
      hnotHalt hlookup htail hmove hfirst
    simp [validatorBlockRightFlipRows, a]
  have haction3 :
      validatorKeepPhysicalRow (a 3) read.secondBit Direction.right (a 4) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockRightFlipRow_mem_logicalRows
      hnotHalt hlookup htail hmove hfirst
    simp [validatorBlockRightFlipRows, a]
  have haction4 :
      validatorKeepPhysicalRow (a 4) read.thirdBit Direction.right (a 5) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockRightFlipRow_mem_logicalRows
      hnotHalt hlookup htail hmove hfirst
    simp [validatorBlockRightFlipRows, a]
  have haction5 :
      validatorKeepPhysicalRow (a 5) read.fourthBit Direction.right
          (validatorBlockRootState row.target) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockRightFlipRow_mem_logicalRows
      hnotHalt hlookup htail hmove hfirst
    simp [validatorBlockRightFlipRows, a]
  have hstep3 :
      M.runConfig 1
          { state := validatorBlockDecode3State logical
              read.firstBit read.secondBit read.thirdBit
            tape := tape3 } =
        { state := a 0, tape := tape4 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical hleaf tape3 hread3
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite3, tape4] using hrun
  have hstep4 : M.runConfig 1 { state := a 0, tape := tape4 } =
      { state := a 1, tape := tape5 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction0 tape4 hread4
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite4, tape5] using hrun
  have hstep5 : M.runConfig 1 { state := a 1, tape := tape5 } =
      { state := a 2, tape := tape6 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction1 tape5 hread5
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite5, tape6] using hrun
  have hstep6 : M.runConfig 1 { state := a 2, tape := tape6 } =
      { state := a 3, tape := tape7 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction2 tape6 hread6
    simpa [validatorPhysicalRow, tape7] using hrun
  have hstep7 : M.runConfig 1 { state := a 3, tape := tape7 } =
      { state := a 4, tape := tape8 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction3 tape7 hread7
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite7, tape8] using hrun
  have hstep8 : M.runConfig 1 { state := a 4, tape := tape8 } =
      { state := a 5, tape := tape9 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction4 tape8 hread8
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite8, tape9] using hrun
  have hstep9 : M.runConfig 1 { state := a 5, tape := tape9 } =
      { state := validatorBlockRootState row.target, tape := tape10 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction5 tape9 hread9
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite9, tape10] using hrun
  have hreach3 : ValidatorBlockPhysicalReaches M
      { state := validatorBlockDecode3State logical
          read.firstBit read.secondBit read.thirdBit, tape := tape3 }
      { state := a 0, tape := tape4 } := ⟨1, hstep3⟩
  have hreach4 : ValidatorBlockPhysicalReaches M
      { state := a 0, tape := tape4 } { state := a 1, tape := tape5 } :=
    ⟨1, hstep4⟩
  have hreach5 : ValidatorBlockPhysicalReaches M
      { state := a 1, tape := tape5 } { state := a 2, tape := tape6 } :=
    ⟨1, hstep5⟩
  have hreach6 : ValidatorBlockPhysicalReaches M
      { state := a 2, tape := tape6 } { state := a 3, tape := tape7 } :=
    ⟨1, hstep6⟩
  have hreach7 : ValidatorBlockPhysicalReaches M
      { state := a 3, tape := tape7 } { state := a 4, tape := tape8 } :=
    ⟨1, hstep7⟩
  have hreach8 : ValidatorBlockPhysicalReaches M
      { state := a 4, tape := tape8 } { state := a 5, tape := tape9 } :=
    ⟨1, hstep8⟩
  have hreach9 : ValidatorBlockPhysicalReaches M
      { state := a 5, tape := tape9 }
      { state := validatorBlockRootState row.target, tape := tape10 } :=
    ⟨1, hstep9⟩
  have hreach := hreach3.trans hreach4 |>.trans hreach5 |>.trans hreach6
    |>.trans hreach7 |>.trans hreach8 |>.trans hreach9
  have hphysical := validatorPhysicalizeBlockTape_write_moveRight
    left right read row.write htailRead
  have hfinal : tape10 = validatorPhysicalizeBlockTape
      (Tape.move Direction.right
        (Tape.write (some row.write)
          { left := left, head := some read, right := right })) := by
    rw [hphysical]
    rfl
  rcases hreach with ⟨steps, hreach⟩
  exact ⟨steps, by rw [hreach, hfinal]⟩

private theorem physicallyReaches_finishValidatorBlock_left
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall physicalRow : TransitionDescription,
      physicalRow ∈ (compileValidatorBlockDescription D).transitions ->
        physicalRow ∈ M.transitions)
    (hdet : M.Deterministic)
    {logical : Nat} (hlogical : logical < D.stateCount)
    (hnotHalt : logical ≠ D.halt)
    {read : ValidatorBlockSymbol} {row : ValidatorBlockTransition}
    (hlookup : D.lookup logical read = some row)
    (htail : row.read.tailBits = row.write.tailBits)
    (hmove : row.move = Direction.left)
    (left right : List (Option ValidatorBlockSymbol)) :
    ValidatorBlockPhysicalReaches M
      { state := validatorBlockDecode3State logical
          read.firstBit read.secondBit read.thirdBit
        tape := validatorBlockDecodedTape
          (validatorPhysicalizeBlockTape
            { left := left, head := some read, right := right }) }
      { state := validatorBlockRootState row.target
        tape := validatorPhysicalizeBlockTape
          (Tape.move Direction.left
            (Tape.write (some row.write)
              { left := left, head := some read, right := right })) } := by
  have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
  have htailRead : read.tailBits = row.write.tailBits := by
    rw [← hreadEq]
    exact htail
  let tape0 := validatorPhysicalizeBlockTape
    { left := left, head := some read, right := right }
  let tape3 := validatorBlockDecodedTape tape0
  let tape4 := Tape.move Direction.left tape3
  let tape5 := Tape.move Direction.left tape4
  let tape6 := Tape.move Direction.left tape5
  let tape7 := Tape.move Direction.left
    (Tape.write (some row.write.firstBit) tape6)
  have hread3 : Tape.read tape3 = some read.fourthBit := by
    simp [tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveRight, tapeAtCells]
  have hread4 : Tape.read tape4 = some read.thirdBit := by
    simp [tape4, tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  have hread5 : Tape.read tape5 = some read.secondBit := by
    simp [tape5, tape4, tape3, tape0, validatorBlockDecodedTape,
      validatorPhysicalizeBlockTape, validatorBlockCellBits,
      ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  have hread6 : Tape.read tape6 = some read.firstBit := by
    simp [tape6, tape5, tape4, tape3, tape0,
      validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
      validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
      Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]
  have hwrite3 : Tape.write (some read.fourthBit) tape3 = tape3 := by
    rw [← hread3]
    exact Tape.write_read_eq_self tape3
  have hwrite4 : Tape.write (some read.thirdBit) tape4 = tape4 := by
    rw [← hread4]
    exact Tape.write_read_eq_self tape4
  have hwrite5 : Tape.write (some read.secondBit) tape5 = tape5 := by
    rw [← hread5]
    exact Tape.write_read_eq_self tape5
  let a := validatorBlockActionState logical read
  have hleaf :
      validatorKeepPhysicalRow
          (validatorBlockDecode3State logical
            read.firstBit read.secondBit read.thirdBit)
          read.fourthBit Direction.left (a 0) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockLeafRow_mem_logicalRows hnotHalt read
    simp [validatorBlockLeafRows, hlookup, htail, hmove, a]
  have haction0 :
      validatorKeepPhysicalRow (a 0) read.thirdBit Direction.left (a 1) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockLeftRow_mem_logicalRows
      hnotHalt hlookup htail hmove
    simp [validatorBlockLeftRows, a]
  have haction1 :
      validatorKeepPhysicalRow (a 1) read.secondBit Direction.left (a 2) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockLeftRow_mem_logicalRows
      hnotHalt hlookup htail hmove
    simp [validatorBlockLeftRows, a]
  have haction2 :
      validatorPhysicalRow (a 2) read.firstBit row.write.firstBit
          Direction.left (a 3) ∈
        validatorBlockLogicalRows D logical := by
    apply validatorBlockLeftRow_mem_logicalRows
      hnotHalt hlookup htail hmove
    simp [validatorBlockLeftRows, a]
  have hstep3 :
      M.runConfig 1
          { state := validatorBlockDecode3State logical
              read.firstBit read.secondBit read.thirdBit
            tape := tape3 } =
        { state := a 0, tape := tape4 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical hleaf tape3 hread3
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite3, tape4] using hrun
  have hstep4 : M.runConfig 1 { state := a 0, tape := tape4 } =
      { state := a 1, tape := tape5 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction0 tape4 hread4
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite4, tape5] using hrun
  have hstep5 : M.runConfig 1 { state := a 1, tape := tape5 } =
      { state := a 2, tape := tape6 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction1 tape5 hread5
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      hwrite5, tape6] using hrun
  have hstep6 : M.runConfig 1 { state := a 2, tape := tape6 } =
      { state := a 3, tape := tape7 } := by
    have hrun := runConfig_one_of_validatorBlockLogicalRow
      hsubset hdet hlogical haction2 tape6 hread6
    simpa [validatorPhysicalRow, tape7] using hrun
  have hreach3 : ValidatorBlockPhysicalReaches M
      { state := validatorBlockDecode3State logical
          read.firstBit read.secondBit read.thirdBit, tape := tape3 }
      { state := a 0, tape := tape4 } := ⟨1, hstep3⟩
  have hreach4 : ValidatorBlockPhysicalReaches M
      { state := a 0, tape := tape4 } { state := a 1, tape := tape5 } :=
    ⟨1, hstep4⟩
  have hreach5 : ValidatorBlockPhysicalReaches M
      { state := a 1, tape := tape5 } { state := a 2, tape := tape6 } :=
    ⟨1, hstep5⟩
  have hreach6 : ValidatorBlockPhysicalReaches M
      { state := a 2, tape := tape6 } { state := a 3, tape := tape7 } :=
    ⟨1, hstep6⟩
  have hcommon := hreach3.trans hreach4 |>.trans hreach5 |>.trans hreach6
  cases left with
  | nil =>
      let tape8 := Tape.move Direction.right tape7
      let tape9 := Tape.move Direction.left tape8
      have hread7 : Tape.read tape7 = none := by
        simp [tape7, tape6, tape5, tape4, tape3, tape0,
          validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
          validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          tapeAtCells]
      have hread8 : Tape.read tape8 = some row.write.firstBit := by
        simp [tape8, tape7, tape6, tape5, tape4, tape3, tape0,
          validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
          validatorBlockCellBits, ValidatorBlockSymbol.bits_eq_components,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          tapeAtCells]
      have hwrite7 : Tape.write none tape7 = tape7 := by
        rw [← hread7]
        exact Tape.write_read_eq_self tape7
      have hwrite8 : Tape.write (some row.write.firstBit) tape8 = tape8 := by
        rw [← hread8]
        exact Tape.write_read_eq_self tape8
      have haction3 :
          { source := a 3, read := none, write := none
            move := Direction.right
            target := validatorBlockBoundaryState logical read } ∈
            validatorBlockLogicalRows D logical := by
        apply validatorBlockLeftRow_mem_logicalRows
          hnotHalt hlookup htail hmove
        simp [validatorBlockLeftRows, a]
      have hboundary :
          validatorKeepPhysicalRow
              (validatorBlockBoundaryState logical read)
              row.write.firstBit Direction.left
              (validatorBlockRootState row.target) ∈
            validatorBlockLogicalRows D logical := by
        apply validatorBlockLeftRow_mem_logicalRows
          hnotHalt hlookup htail hmove
        simp [validatorBlockLeftRows]
      have hstep7 : M.runConfig 1 { state := a 3, tape := tape7 } =
          { state := validatorBlockBoundaryState logical read
            tape := tape8 } := by
        have hrun := runConfig_one_of_validatorBlockLogicalRow
          hsubset hdet hlogical haction3 tape7 hread7
        simpa [hwrite7, tape8] using hrun
      have hstep8 : M.runConfig 1
          { state := validatorBlockBoundaryState logical read
            tape := tape8 } =
          { state := validatorBlockRootState row.target, tape := tape9 } := by
        have hrun := runConfig_one_of_validatorBlockLogicalRow
          hsubset hdet hlogical hboundary tape8 hread8
        simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
          hwrite8, tape9] using hrun
      have hreach7 : ValidatorBlockPhysicalReaches M
          { state := a 3, tape := tape7 }
          { state := validatorBlockBoundaryState logical read
            tape := tape8 } := ⟨1, hstep7⟩
      have hreach8 : ValidatorBlockPhysicalReaches M
          { state := validatorBlockBoundaryState logical read
            tape := tape8 }
          { state := validatorBlockRootState row.target, tape := tape9 } :=
        ⟨1, hstep8⟩
      have hreach := hcommon.trans hreach7 |>.trans hreach8
      have hphysical := validatorPhysicalizeBlockTape_write_moveLeft_nil
        right read row.write htailRead
      have hfinal : tape9 = validatorPhysicalizeBlockTape
          (Tape.move Direction.left
            (Tape.write (some row.write)
              { left := [], head := some read, right := right })) := by
        rw [hphysical]
        rfl
      rcases hreach with ⟨steps, hreach⟩
      exact ⟨steps, by rw [hreach, hfinal]⟩
  | cons previous left =>
      cases previous with
      | none =>
          let tape8 := Tape.move Direction.right tape7
          let tape9 := Tape.move Direction.left tape8
          have hread7 : Tape.read tape7 = none := by
            simp [tape7, tape6, tape5, tape4, tape3, tape0,
              validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
              validatorBlockCellBits,
              ValidatorBlockSymbol.bits_eq_components,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells]
          have hread8 : Tape.read tape8 = some row.write.firstBit := by
            simp [tape8, tape7, tape6, tape5, tape4, tape3, tape0,
              validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
              validatorBlockCellBits,
              ValidatorBlockSymbol.bits_eq_components,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells]
          have hwrite7 : Tape.write none tape7 = tape7 := by
            rw [← hread7]
            exact Tape.write_read_eq_self tape7
          have hwrite8 :
              Tape.write (some row.write.firstBit) tape8 = tape8 := by
            rw [← hread8]
            exact Tape.write_read_eq_self tape8
          have haction3 :
              { source := a 3, read := none, write := none
                move := Direction.right
                target := validatorBlockBoundaryState logical read } ∈
                validatorBlockLogicalRows D logical := by
            apply validatorBlockLeftRow_mem_logicalRows
              hnotHalt hlookup htail hmove
            simp [validatorBlockLeftRows, a]
          have hboundary :
              validatorKeepPhysicalRow
                  (validatorBlockBoundaryState logical read)
                  row.write.firstBit Direction.left
                  (validatorBlockRootState row.target) ∈
                validatorBlockLogicalRows D logical := by
            apply validatorBlockLeftRow_mem_logicalRows
              hnotHalt hlookup htail hmove
            simp [validatorBlockLeftRows]
          have hstep7 : M.runConfig 1 { state := a 3, tape := tape7 } =
              { state := validatorBlockBoundaryState logical read
                tape := tape8 } := by
            have hrun := runConfig_one_of_validatorBlockLogicalRow
              hsubset hdet hlogical haction3 tape7 hread7
            simpa [hwrite7, tape8] using hrun
          have hstep8 : M.runConfig 1
              { state := validatorBlockBoundaryState logical read
                tape := tape8 } =
              { state := validatorBlockRootState row.target
                tape := tape9 } := by
            have hrun := runConfig_one_of_validatorBlockLogicalRow
              hsubset hdet hlogical hboundary tape8 hread8
            simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
              hwrite8, tape9] using hrun
          have hreach7 : ValidatorBlockPhysicalReaches M
              { state := a 3, tape := tape7 }
              { state := validatorBlockBoundaryState logical read
                tape := tape8 } := ⟨1, hstep7⟩
          have hreach8 : ValidatorBlockPhysicalReaches M
              { state := validatorBlockBoundaryState logical read
                tape := tape8 }
              { state := validatorBlockRootState row.target
                tape := tape9 } := ⟨1, hstep8⟩
          have hreach := hcommon.trans hreach7 |>.trans hreach8
          have hphysical :=
            validatorPhysicalizeBlockTape_write_moveLeft_none
              left right read row.write htailRead
          have hfinal : tape9 = validatorPhysicalizeBlockTape
              (Tape.move Direction.left
                (Tape.write (some row.write)
                  { left := none :: left
                    head := some read
                    right := right })) := by
            rw [hphysical]
            rfl
          rcases hreach with ⟨steps, hreach⟩
          exact ⟨steps, by rw [hreach, hfinal]⟩
      | some previous =>
          let tape8 := Tape.move Direction.left tape7
          let tape9 := Tape.move Direction.left tape8
          let tape10 := Tape.move Direction.left tape9
          have hread7 : Tape.read tape7 = some previous.fourthBit := by
            simp [tape7, tape6, tape5, tape4, tape3, tape0,
              validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
              validatorBlockCellBits,
              ValidatorBlockSymbol.bits_eq_components,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells]
          have hread8 : Tape.read tape8 = some previous.thirdBit := by
            simp [tape8, tape7, tape6, tape5, tape4, tape3, tape0,
              validatorBlockDecodedTape, validatorPhysicalizeBlockTape,
              validatorBlockCellBits,
              ValidatorBlockSymbol.bits_eq_components,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells]
          have hread9 : Tape.read tape9 = some previous.secondBit := by
            simp [tape9, tape8, tape7, tape6, tape5, tape4, tape3,
              tape0, validatorBlockDecodedTape,
              validatorPhysicalizeBlockTape, validatorBlockCellBits,
              ValidatorBlockSymbol.bits_eq_components,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells]
          have hwrite7 :
              Tape.write (some previous.fourthBit) tape7 = tape7 := by
            rw [← hread7]
            exact Tape.write_read_eq_self tape7
          have hwrite8 :
              Tape.write (some previous.thirdBit) tape8 = tape8 := by
            rw [← hread8]
            exact Tape.write_read_eq_self tape8
          have hwrite9 :
              Tape.write (some previous.secondBit) tape9 = tape9 := by
            rw [← hread9]
            exact Tape.write_read_eq_self tape9
          have haction3 :
              validatorKeepPhysicalRow (a 3) previous.fourthBit
                  Direction.left (a 4) ∈
                validatorBlockLogicalRows D logical := by
            apply validatorBlockLeftRow_mem_logicalRows
              hnotHalt hlookup htail hmove
            cases hbit : previous.fourthBit <;>
              simp [validatorBlockLeftRows, validatorKeepEitherRows, a]
          have haction4 :
              validatorKeepPhysicalRow (a 4) previous.thirdBit
                  Direction.left (a 5) ∈
                validatorBlockLogicalRows D logical := by
            apply validatorBlockLeftRow_mem_logicalRows
              hnotHalt hlookup htail hmove
            cases hbit : previous.thirdBit <;>
              simp [validatorBlockLeftRows, validatorKeepEitherRows, a]
          have haction5 :
              validatorKeepPhysicalRow (a 5) previous.secondBit
                  Direction.left (validatorBlockRootState row.target) ∈
                validatorBlockLogicalRows D logical := by
            apply validatorBlockLeftRow_mem_logicalRows
              hnotHalt hlookup htail hmove
            cases hbit : previous.secondBit <;>
              simp [validatorBlockLeftRows, validatorKeepEitherRows, a]
          have hstep7 : M.runConfig 1 { state := a 3, tape := tape7 } =
              { state := a 4, tape := tape8 } := by
            have hrun := runConfig_one_of_validatorBlockLogicalRow
              hsubset hdet hlogical haction3 tape7 hread7
            simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
              hwrite7, tape8] using hrun
          have hstep8 : M.runConfig 1 { state := a 4, tape := tape8 } =
              { state := a 5, tape := tape9 } := by
            have hrun := runConfig_one_of_validatorBlockLogicalRow
              hsubset hdet hlogical haction4 tape8 hread8
            simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
              hwrite8, tape9] using hrun
          have hstep9 : M.runConfig 1 { state := a 5, tape := tape9 } =
              { state := validatorBlockRootState row.target
                tape := tape10 } := by
            have hrun := runConfig_one_of_validatorBlockLogicalRow
              hsubset hdet hlogical haction5 tape9 hread9
            simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
              hwrite9, tape10] using hrun
          have hreach7 : ValidatorBlockPhysicalReaches M
              { state := a 3, tape := tape7 }
              { state := a 4, tape := tape8 } := ⟨1, hstep7⟩
          have hreach8 : ValidatorBlockPhysicalReaches M
              { state := a 4, tape := tape8 }
              { state := a 5, tape := tape9 } := ⟨1, hstep8⟩
          have hreach9 : ValidatorBlockPhysicalReaches M
              { state := a 5, tape := tape9 }
              { state := validatorBlockRootState row.target
                tape := tape10 } := ⟨1, hstep9⟩
          have hreach := hcommon.trans hreach7 |>.trans hreach8
            |>.trans hreach9
          have hphysical :=
            validatorPhysicalizeBlockTape_write_moveLeft_some
              left right previous read row.write htailRead
          have hfinal : tape10 = validatorPhysicalizeBlockTape
              (Tape.move Direction.left
                (Tape.write (some row.write)
                  { left := some previous :: left
                    head := some read
                    right := right })) := by
            rw [hphysical]
            rfl
          rcases hreach with ⟨steps, hreach⟩
          exact ⟨steps, by rw [hreach, hfinal]⟩

/-- One logical aligned-block step is simulated exactly by generated rows. -/
theorem validatorBlockPhysicalReaches_of_stepConfig
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall physicalRow : TransitionDescription,
      physicalRow ∈ (compileValidatorBlockDescription D).transitions ->
        physicalRow ∈ M.transitions)
    (hdet : M.Deterministic)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {configuration next : ValidatorBlockDescription.Configuration}
    (hstate : configuration.state < D.stateCount)
    (hnotHalt : configuration.state ≠ D.halt)
    (hstep : D.stepConfig configuration = some next) :
    ValidatorBlockPhysicalReaches M
      (validatorPhysicalBlockConfiguration configuration)
      (validatorPhysicalBlockConfiguration next) := by
  rcases configuration with ⟨logical, tape⟩
  rcases tape with ⟨left, head, right⟩
  cases head with
  | none =>
      simp [ValidatorBlockDescription.stepConfig, Tape.read] at hstep
  | some read =>
      cases hlookup : D.lookup logical read with
      | none =>
          simp [ValidatorBlockDescription.stepConfig, Tape.read,
            hlookup] at hstep
      | some row =>
          simp [ValidatorBlockDescription.stepConfig, Tape.read,
            hlookup] at hstep
          cases hstep
          have htail := htailCompatible logical read row hlookup
          have hdecodeRun := runConfig_decodeValidatorBlock
            hsubset hdet hstate hnotHalt left right read
          have hdecode : ValidatorBlockPhysicalReaches M
              (validatorPhysicalBlockConfiguration
                { state := logical
                  tape := { left := left, head := some read, right := right } })
              { state := validatorBlockDecode3State logical
                  read.firstBit read.secondBit read.thirdBit
                tape := validatorBlockDecodedTape
                  (validatorPhysicalizeBlockTape
                    { left := left, head := some read, right := right }) } :=
            ⟨3, by
              simpa [validatorPhysicalBlockConfiguration,
                validatorBlockDecodedTape] using hdecodeRun⟩
          cases hmove : row.move with
          | right =>
              by_cases hfirst : row.read.firstBit = row.write.firstBit
              · have hfinishRun := runConfig_finishValidatorBlock_right_same
                  hsubset hdet hstate hnotHalt hlookup htail hmove hfirst
                  left right
                have hfinish : ValidatorBlockPhysicalReaches M
                    { state := validatorBlockDecode3State logical
                        read.firstBit read.secondBit read.thirdBit
                      tape := validatorBlockDecodedTape
                        (validatorPhysicalizeBlockTape
                          { left := left, head := some read, right := right }) }
                    (validatorPhysicalBlockConfiguration
                      { state := row.target
                        tape := Tape.move Direction.right
                          (Tape.write (some row.write)
                            { left := left
                              head := some read
                              right := right }) }) :=
                  ⟨1, by
                    simpa [validatorPhysicalBlockConfiguration]
                      using hfinishRun⟩
                exact hdecode.trans hfinish
              · have hfinish :=
                  physicallyReaches_finishValidatorBlock_right_flip
                    hsubset hdet hstate hnotHalt hlookup htail hmove hfirst
                    left right
                exact hdecode.trans (by
                  simpa [validatorPhysicalBlockConfiguration] using hfinish)
          | left =>
              have hfinish := physicallyReaches_finishValidatorBlock_left
                hsubset hdet hstate hnotHalt hlookup htail hmove left right
              exact hdecode.trans (by
                simpa [validatorPhysicalBlockConfiguration] using hfinish)

/-- Generated rows simulate an arbitrary fuel-bounded logical execution. -/
theorem validatorBlockPhysicalReaches_runConfig
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall physicalRow : TransitionDescription,
      physicalRow ∈ (compileValidatorBlockDescription D).transitions ->
        physicalRow ∈ M.transitions)
    (hdet : M.Deterministic)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    (steps : Nat) (configuration : ValidatorBlockDescription.Configuration) :
    ValidatorBlockPhysicalReaches M
      (validatorPhysicalBlockConfiguration configuration)
      (validatorPhysicalBlockConfiguration
        (D.runConfig steps configuration)) := by
  induction steps generalizing configuration with
  | zero =>
      exact validatorBlockPhysicalReaches_refl M _
  | succ steps ih =>
      cases hstep : D.stepConfig configuration with
      | none =>
          simpa [ValidatorBlockDescription.runConfig, hstep] using
            validatorBlockPhysicalReaches_refl M
              (validatorPhysicalBlockConfiguration configuration)
      | some next =>
          have hone := validatorBlockPhysicalReaches_of_stepConfig
            hsubset hdet htailCompatible
            (ValidatorBlockDescription.state_lt_of_stepConfig
              hsourceBound hstep)
            (ValidatorBlockDescription.state_ne_halt_of_stepConfig
              hhaltFree hstep)
            hstep
          have htail := ih next
          simpa [ValidatorBlockDescription.runConfig, hstep] using
            hone.trans htail

/-- Lift logical reflexive-transitive reachability to the Boolean compiler. -/
theorem validatorBlockPhysicalReaches_of_logicalReaches
    {D : ValidatorBlockDescription} {M : MachineDescription}
    (hsubset : forall physicalRow : TransitionDescription,
      physicalRow ∈ (compileValidatorBlockDescription D).transitions ->
        physicalRow ∈ M.transitions)
    (hdet : M.Deterministic)
    (hsourceBound : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source < D.stateCount)
    (hhaltFree : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.source ≠ D.halt)
    (htailCompatible : forall state read row,
      D.lookup state read = some row ->
        row.read.tailBits = row.write.tailBits)
    {source target : ValidatorBlockDescription.Configuration}
    (hreaches : D.Reaches source target) :
    ValidatorBlockPhysicalReaches M
      (validatorPhysicalBlockConfiguration source)
      (validatorPhysicalBlockConfiguration target) := by
  rcases hreaches with ⟨steps, hrun⟩
  have hphysical := validatorBlockPhysicalReaches_runConfig
    hsubset hdet hsourceBound hhaltFree htailCompatible steps source
  simpa [hrun] using hphysical

end SelfHaltingRecognizer
end Computability
end FoC

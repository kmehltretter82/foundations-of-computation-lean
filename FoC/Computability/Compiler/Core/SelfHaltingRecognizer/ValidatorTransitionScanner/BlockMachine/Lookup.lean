import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.BlockMachine.Entry
import FoC.Computability.Compiler.Core.TransitionTableChecks

set_option doc.verso true

/-!
# Generated block compiler lookup inversion

This module proves missing-transition facts from the symbolic row generators.
The proofs avoid normalizing a complete generated transition table.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open MachineDescription

private theorem validatorBlockLeafState_range
    (logical : Nat) (read : ValidatorBlockSymbol) :
    validatorBlockRootState logical + 7 ≤
        validatorBlockLeafState logical read ∧
      validatorBlockLeafState logical read <
        validatorBlockRootState logical + 15 := by
  cases read <;>
    simp [validatorBlockLeafState, validatorBlockDecode3State,
      validatorBlockBoolCode, ValidatorBlockSymbol.firstBit,
      ValidatorBlockSymbol.secondBit, ValidatorBlockSymbol.thirdBit] <;>
    lia

private theorem validatorBlockActionState_range
    (logical : Nat) (read : ValidatorBlockSymbol) (phase : Nat)
    (hphase : phase < 7) :
    validatorBlockRootState logical + 15 ≤
        validatorBlockActionState logical read phase ∧
      validatorBlockActionState logical read phase <
        validatorBlockRootState logical + validatorBlockStateWidth := by
  cases read <;>
    simp [validatorBlockActionState, validatorBlockStateWidth,
      ValidatorBlockSymbol.toNat] at * <;>
    lia

private theorem validatorBlockDecoderRows_source_range
    {logical : Nat} {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockDecoderRows logical) :
    validatorBlockRootState logical ≤ physicalRow.source ∧
      physicalRow.source < validatorBlockRootState logical + 7 := by
  simp only [validatorBlockDecoderRows, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [validatorKeepPhysicalRow, validatorPhysicalRow,
      validatorBlockDecode1State, validatorBlockDecode2State,
      validatorBlockDecode3State, validatorBlockBoolCode] <;>
    lia

private theorem validatorBlockDecoderRows_read_some
    {logical : Nat} {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockDecoderRows logical) :
    exists bit : Bool, physicalRow.read = some bit := by
  simp only [validatorBlockDecoderRows, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [validatorKeepPhysicalRow, validatorPhysicalRow]

private theorem validatorBlockLeafRows_key
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockLeafRows D logical read) :
    physicalRow.source = validatorBlockLeafState logical read ∧
      physicalRow.read = some read.fourthBit ∧
        exists row : ValidatorBlockTransition,
          D.lookup logical read = some row := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockLeafRows, hlookup] at hmem
  | some row =>
      by_cases htail : row.read.tailBits = row.write.tailBits
      · by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · simp [validatorBlockLeafRows, hlookup, htail, hmove, hfirst]
              at hmem
            subst physicalRow
            exact ⟨rfl, rfl, row, rfl⟩
          · simp [validatorBlockLeafRows, hlookup, htail, hmove, hfirst]
              at hmem
            subst physicalRow
            exact ⟨rfl, rfl, row, rfl⟩
        · simp [validatorBlockLeafRows, hlookup, htail, hmove] at hmem
          subst physicalRow
          exact ⟨rfl, rfl, row, rfl⟩
      · simp [validatorBlockLeafRows, hlookup, htail] at hmem

private theorem validatorBlockRightFlipRows_source_range
    {logical : Nat} {read write : ValidatorBlockSymbol} {target : Nat}
    {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈
      validatorBlockRightFlipRows logical read write target) :
    validatorBlockRootState logical + 15 ≤ physicalRow.source ∧
      physicalRow.source <
        validatorBlockRootState logical + validatorBlockStateWidth := by
  simp only [validatorBlockRightFlipRows, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow] using
      validatorBlockActionState_range logical read _ (by decide)

private theorem validatorBlockLeftRows_source_range
    {logical : Nat} {read write : ValidatorBlockSymbol} {target : Nat}
    {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockLeftRows logical read write target) :
    validatorBlockRootState logical + 15 ≤ physicalRow.source ∧
      physicalRow.source <
        validatorBlockRootState logical + validatorBlockStateWidth := by
  simp only [validatorBlockLeftRows, validatorKeepEitherRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    (((((rfl | rfl | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | rfl
  all_goals
    simpa [validatorKeepPhysicalRow, validatorPhysicalRow,
      validatorBlockBoundaryState] using
      validatorBlockActionState_range logical read _ (by decide)

private theorem validatorBlockActionRows_source_range
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockActionRows D logical read) :
    validatorBlockRootState logical + 15 ≤ physicalRow.source ∧
      physicalRow.source <
        validatorBlockRootState logical + validatorBlockStateWidth := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockActionRows, hlookup] at hmem
  | some row =>
      by_cases htail : row.read.tailBits = row.write.tailBits
      · by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · simp [validatorBlockActionRows, hlookup, htail, hmove, hfirst]
              at hmem
          · exact validatorBlockRightFlipRows_source_range
              (by simpa [validatorBlockActionRows, hlookup, htail, hmove,
                hfirst] using hmem)
        · exact validatorBlockLeftRows_source_range
            (by simpa [validatorBlockActionRows, hlookup, htail, hmove]
              using hmem)
      · simp [validatorBlockActionRows, hlookup, htail] at hmem

private theorem validatorBlockLogicalRows_cases
    {D : ValidatorBlockDescription} {logical : Nat}
    {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockLogicalRows D logical) :
    physicalRow ∈ validatorBlockDecoderRows logical ∨
      (exists read : ValidatorBlockSymbol,
        physicalRow ∈ validatorBlockLeafRows D logical read) ∨
      exists read : ValidatorBlockSymbol,
        physicalRow ∈ validatorBlockActionRows D logical read := by
  by_cases hhalt : logical = D.halt
  · simp [validatorBlockLogicalRows, hhalt] at hmem
  · simp only [validatorBlockLogicalRows, if_neg hhalt,
      List.mem_append] at hmem
    rcases hmem with (hdecoder | hleaf) | haction
    · exact Or.inl hdecoder
    · rw [List.mem_flatMap] at hleaf
      rcases hleaf with ⟨read, _hread, hleaf⟩
      exact Or.inr (Or.inl ⟨read, hleaf⟩)
    · rw [List.mem_flatMap] at haction
      rcases haction with ⟨read, _hread, haction⟩
      exact Or.inr (Or.inr ⟨read, haction⟩)

private theorem validatorBlockLogicalRows_source_range
    {D : ValidatorBlockDescription} {logical : Nat}
    {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockLogicalRows D logical) :
    validatorBlockRootState logical ≤ physicalRow.source ∧
      physicalRow.source <
        validatorBlockRootState logical + validatorBlockStateWidth := by
  rcases validatorBlockLogicalRows_cases hmem with
    hdecoder | ⟨read, hleaf⟩ | ⟨read, haction⟩
  · have hrange := validatorBlockDecoderRows_source_range hdecoder
    exact ⟨hrange.1, Nat.lt_trans hrange.2 (by
      simp [validatorBlockStateWidth])⟩
  · have hkey := validatorBlockLeafRows_key hleaf
    rw [hkey.1]
    have hrange := validatorBlockLeafState_range logical read
    exact ⟨Nat.le_trans (by lia) hrange.1,
      Nat.lt_trans hrange.2 (by simp [validatorBlockStateWidth])⟩
  · have hrange := validatorBlockActionRows_source_range haction
    exact ⟨Nat.le_trans (by lia) hrange.1, hrange.2⟩

private theorem compiledRow_mem_logicalRows
    {D : ValidatorBlockDescription} {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈
      (compileValidatorBlockDescription D).transitions) :
    exists logical : Nat,
      logical < D.stateCount ∧
        physicalRow ∈ validatorBlockLogicalRows D logical := by
  rw [compileValidatorBlockDescription, validatorBlockTransitionChunks,
    List.mem_flatten] at hmem
  rcases hmem with ⟨rows, hrows, hmem⟩
  rw [List.mem_map] at hrows
  rcases hrows with ⟨logical, hlogical, rfl⟩
  exact ⟨logical, List.mem_range.mp hlogical, hmem⟩

private theorem validatorBlockLogical_eq_of_ranges
    {left right source : Nat}
    (hleft : validatorBlockRootState left ≤ source ∧
      source < validatorBlockRootState left + validatorBlockStateWidth)
    (hright : validatorBlockRootState right ≤ source ∧
      source < validatorBlockRootState right + validatorBlockStateWidth) :
    left = right := by
  rcases Nat.lt_trichotomy left right with hlt | heq | hgt
  · exfalso
    simp [validatorBlockRootState, validatorBlockStateWidth] at hleft hright
    lia
  · exact heq
  · exfalso
    simp [validatorBlockRootState, validatorBlockStateWidth] at hleft hright
    lia

private theorem validatorBlockSymbol_eq_of_leaf_key
    {logical : Nat} {left right : ValidatorBlockSymbol}
    (hstate : validatorBlockLeafState logical left =
      validatorBlockLeafState logical right)
    (hread : left.fourthBit = right.fourthBit) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [validatorBlockLeafState, validatorBlockDecode3State,
      validatorBlockBoolCode, ValidatorBlockSymbol.firstBit,
      ValidatorBlockSymbol.secondBit, ValidatorBlockSymbol.thirdBit,
      ValidatorBlockSymbol.fourthBit]

/-- A generated block root has no transition on a physical blank. -/
theorem compileValidatorBlockDescription_lookup_root_none
    (D : ValidatorBlockDescription) (logical : Nat) :
    (compileValidatorBlockDescription D).lookupTransition
        (validatorBlockRootState logical) none = none := by
  unfold MachineDescription.lookupTransition
  apply List.find?_eq_none.mpr
  intro physicalRow hmem
  by_cases hsource : physicalRow.source = validatorBlockRootState logical
  · have hcompiled := compiledRow_mem_logicalRows hmem
    rcases hcompiled with ⟨owner, _howner, hrow⟩
    have hownerRange := validatorBlockLogicalRows_source_range hrow
    have hlogicalRange :
        validatorBlockRootState logical ≤ physicalRow.source ∧
          physicalRow.source <
            validatorBlockRootState logical + validatorBlockStateWidth := by
      rw [hsource]
      simp [validatorBlockStateWidth]
    have hownerEq := validatorBlockLogical_eq_of_ranges
      hownerRange hlogicalRange
    subst owner
    rcases validatorBlockLogicalRows_cases hrow with
      hdecoder | ⟨read, hleaf⟩ | ⟨read, haction⟩
    · rcases validatorBlockDecoderRows_read_some hdecoder with ⟨bit, hread⟩
      simp [MachineDescription.Matches, hsource, hread]
    · have hkey := validatorBlockLeafRows_key hleaf
      have hrange := validatorBlockLeafState_range logical read
      simp [MachineDescription.Matches, hsource]
      rw [hkey.1] at hsource
      lia
    · have hrange := validatorBlockActionRows_source_range haction
      simp [MachineDescription.Matches, hsource]
      lia
  · simp [MachineDescription.Matches, hsource]

/-- If a logical row is absent, its generated decoder leaf has no outgoing
physical transition. -/
theorem compileValidatorBlockDescription_lookup_leaf_none
    (D : ValidatorBlockDescription) (logical : Nat)
    (read : ValidatorBlockSymbol)
    (hlookup : D.lookup logical read = none) :
    (compileValidatorBlockDescription D).lookupTransition
        (validatorBlockLeafState logical read) (some read.fourthBit) = none := by
  unfold MachineDescription.lookupTransition
  apply List.find?_eq_none.mpr
  intro physicalRow hmem
  by_cases hsource :
      physicalRow.source = validatorBlockLeafState logical read
  · by_cases hread : physicalRow.read = some read.fourthBit
    · have hcompiled := compiledRow_mem_logicalRows hmem
      rcases hcompiled with ⟨owner, _howner, hrow⟩
      have hownerRange := validatorBlockLogicalRows_source_range hrow
      have hleafRange := validatorBlockLeafState_range logical read
      have hlogicalRange :
          validatorBlockRootState logical ≤ physicalRow.source ∧
            physicalRow.source <
              validatorBlockRootState logical + validatorBlockStateWidth := by
        rw [hsource]
        exact ⟨Nat.le_trans (by lia) hleafRange.1,
          Nat.lt_trans hleafRange.2 (by simp [validatorBlockStateWidth])⟩
      have hownerEq := validatorBlockLogical_eq_of_ranges
        hownerRange hlogicalRange
      subst owner
      rcases validatorBlockLogicalRows_cases hrow with
        hdecoder | ⟨candidate, hleaf⟩ | ⟨candidate, haction⟩
      · have hdecoderRange := validatorBlockDecoderRows_source_range hdecoder
        rw [hsource] at hdecoderRange
        lia
      · have hkey := validatorBlockLeafRows_key hleaf
        have hstate : validatorBlockLeafState logical candidate =
            validatorBlockLeafState logical read := by
          rw [← hkey.1, hsource]
        have hfourth : candidate.fourthBit = read.fourthBit := by
          simpa [hkey.2.1] using hread
        have hcand := validatorBlockSymbol_eq_of_leaf_key hstate hfourth
        subst candidate
        rcases hkey.2.2 with ⟨row, hsome⟩
        rw [hlookup] at hsome
        contradiction
      · have hactionRange := validatorBlockActionRows_source_range haction
        rw [hsource] at hactionRange
        lia
    · simp [MachineDescription.Matches, hsource, hread]
  · simp [MachineDescription.Matches, hsource]

/-- Appending the four-left entry rows preserves a core lookup below the
core's state-count boundary. -/
theorem lookupTransition_withValidatorFourLeftEntry_eq_none
    (core : MachineDescription) (state : Nat) (read : Option Bool)
    (hstate : state < core.stateCount)
    (hcore : core.lookupTransition state read = none) :
    (withValidatorFourLeftEntry core).lookupTransition state read = none := by
  unfold MachineDescription.lookupTransition at hcore ⊢
  rw [withValidatorFourLeftEntry, List.find?_append, hcore]
  apply List.find?_eq_none.mpr
  intro row hrow
  simp only [validatorFourLeftEntryRows, List.mem_append,
    validatorFourLeftEntryRowsAt, List.mem_cons, List.not_mem_nil,
    or_false] at hrow
  rcases hrow with
    (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl)
  all_goals
    simp [MachineDescription.Matches, validatorFourLeftEntryRow,
      validatorFourLeftEntryState] <;>
    lia

private theorem transitionKeyRanksAdjacentIncreasingBool_cons_cons
    (first second : TransitionDescription)
    (rest : List TransitionDescription) :
    transitionKeyRanksAdjacentIncreasingBool (first :: second :: rest) =
      (decide (transitionKeyRank first < transitionKeyRank second) &&
        transitionKeyRanksAdjacentIncreasingBool (second :: rest)) := by
  rfl

private theorem transitionKeyRanksAdjacentIncreasingBool_singleton
    (row : TransitionDescription) :
    transitionKeyRanksAdjacentIncreasingBool [row] = true := by
  rfl

private theorem validatorBlockDecoderRows_deterministic
    {logical : Nat} {left right : TransitionDescription}
    (hleft : left ∈ validatorBlockDecoderRows logical)
    (hright : right ∈ validatorBlockDecoderRows logical)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  apply transition_deterministic_of_keyRanksAdjacentIncreasingBool
      (rows := validatorBlockDecoderRows logical) ?_
      left right hleft hright hkey
  simp [validatorBlockDecoderRows,
    transitionKeyRanksAdjacentIncreasingBool_cons_cons,
    transitionKeyRanksAdjacentIncreasingBool_singleton,
    transitionKeyRank,
    transitionReadRank, validatorKeepPhysicalRow, validatorPhysicalRow,
    validatorBlockDecode1State, validatorBlockDecode2State,
    validatorBlockDecode3State, validatorBlockBoolCode]
  constructor
  · lia
  constructor
  · lia
  constructor
  · lia
  constructor
  · lia
  constructor <;> lia

private theorem validatorBlockLeafRows_eq_of_mem
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {left right : TransitionDescription}
    (hleft : left ∈ validatorBlockLeafRows D logical read)
    (hright : right ∈ validatorBlockLeafRows D logical read) :
    left = right := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockLeafRows, hlookup] at hleft
  | some row =>
      by_cases htail : row.read.tailBits = row.write.tailBits
      · by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · simp_all [validatorBlockLeafRows]
          · simp_all [validatorBlockLeafRows]
        · simp_all [validatorBlockLeafRows]
      · simp [validatorBlockLeafRows, hlookup, htail] at hleft

private theorem validatorBlockRightFlipRows_deterministic
    {logical : Nat} {read write : ValidatorBlockSymbol} {target : Nat}
    {left right : TransitionDescription}
    (hleft : left ∈
      validatorBlockRightFlipRows logical read write target)
    (hright : right ∈
      validatorBlockRightFlipRows logical read write target)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  simp only [validatorBlockRightFlipRows, List.mem_cons,
    List.not_mem_nil, or_false] at hleft hright
  rcases hleft with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hright with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp_all [TransitionDescription.SameKey,
    TransitionDescription.SameAction, validatorKeepPhysicalRow,
    validatorPhysicalRow, validatorBlockActionState] <;>
  lia

private theorem validatorBlockLeftRows_deterministic
    {logical : Nat} {read write : ValidatorBlockSymbol} {target : Nat}
    {left right : TransitionDescription}
    (hleft : left ∈ validatorBlockLeftRows logical read write target)
    (hright : right ∈ validatorBlockLeftRows logical read write target)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  simp only [validatorBlockLeftRows, validatorKeepEitherRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      at hleft hright
  rcases hleft with
    (((((rfl | rfl | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | rfl <;>
  rcases hright with
    (((((rfl | rfl | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | rfl <;>
  simp_all [TransitionDescription.SameKey,
    TransitionDescription.SameAction, validatorKeepPhysicalRow,
    validatorPhysicalRow, validatorBlockBoundaryState,
    validatorBlockActionState] <;>
  lia

private theorem validatorBlockRightFlipRows_source_symbol_range
    {logical : Nat} {read write : ValidatorBlockSymbol} {target : Nat}
    {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈
      validatorBlockRightFlipRows logical read write target) :
    validatorBlockActionState logical read 0 ≤ physicalRow.source ∧
      physicalRow.source < validatorBlockActionState logical read 0 + 7 := by
  simp only [validatorBlockRightFlipRows, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [validatorKeepPhysicalRow, validatorPhysicalRow,
      validatorBlockActionState] <;>
    lia

private theorem validatorBlockLeftRows_source_symbol_range
    {logical : Nat} {read write : ValidatorBlockSymbol} {target : Nat}
    {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockLeftRows logical read write target) :
    validatorBlockActionState logical read 0 ≤ physicalRow.source ∧
      physicalRow.source < validatorBlockActionState logical read 0 + 7 := by
  simp only [validatorBlockLeftRows, validatorKeepEitherRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    (((((rfl | rfl | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | rfl
  all_goals
    simp [validatorKeepPhysicalRow, validatorPhysicalRow,
      validatorBlockBoundaryState, validatorBlockActionState] <;>
    lia

private theorem validatorBlockActionRows_source_symbol_range
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {physicalRow : TransitionDescription}
    (hmem : physicalRow ∈ validatorBlockActionRows D logical read) :
    validatorBlockActionState logical read 0 ≤ physicalRow.source ∧
      physicalRow.source < validatorBlockActionState logical read 0 + 7 := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockActionRows, hlookup] at hmem
  | some row =>
      have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
      by_cases htail : row.read.tailBits = row.write.tailBits
      · have htailRead : read.tailBits = row.write.tailBits := by
          rw [← hreadEq]
          exact htail
        by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · simp [validatorBlockActionRows, hlookup, htail, hmove, hfirst]
              at hmem
          · have hfirstRead :
                read.firstBit ≠ row.write.firstBit := by
              rw [← hreadEq]
              exact hfirst
            exact validatorBlockRightFlipRows_source_symbol_range
              (by simpa [validatorBlockActionRows, hlookup, htail, hmove,
                hfirst, hreadEq, htailRead, hfirstRead] using hmem)
        · exact validatorBlockLeftRows_source_symbol_range
            (by simpa [validatorBlockActionRows, hlookup, htail, hmove,
              hreadEq, htailRead]
              using hmem)
      · simp [validatorBlockActionRows, hlookup, htail] at hmem

private theorem validatorBlockActionRows_deterministic
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {left right : TransitionDescription}
    (hleft : left ∈ validatorBlockActionRows D logical read)
    (hright : right ∈ validatorBlockActionRows D logical read)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockActionRows, hlookup] at hleft
  | some row =>
      by_cases htail : row.read.tailBits = row.write.tailBits
      · by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · simp [validatorBlockActionRows, hlookup, htail, hmove, hfirst]
              at hleft
          · apply validatorBlockRightFlipRows_deterministic
              (by simpa [validatorBlockActionRows, hlookup, htail, hmove,
                hfirst] using hleft)
              (by simpa [validatorBlockActionRows, hlookup, htail, hmove,
                hfirst] using hright)
              hkey
        · apply validatorBlockLeftRows_deterministic
            (by simpa [validatorBlockActionRows, hlookup, htail, hmove]
              using hleft)
            (by simpa [validatorBlockActionRows, hlookup, htail, hmove]
              using hright)
            hkey
      · simp [validatorBlockActionRows, hlookup, htail] at hleft

private theorem validatorBlockSymbol_eq_of_action_ranges
    {logical : Nat} {left right : ValidatorBlockSymbol} {source : Nat}
    (hleft : validatorBlockActionState logical left 0 ≤ source ∧
      source < validatorBlockActionState logical left 0 + 7)
    (hright : validatorBlockActionState logical right 0 ≤ source ∧
      source < validatorBlockActionState logical right 0 + 7) :
    left = right := by
  cases left <;> cases right <;>
    simp [validatorBlockActionState, ValidatorBlockSymbol.toNat] at * <;>
    lia

private theorem validatorBlockLogicalRows_deterministic
    {D : ValidatorBlockDescription} {logical : Nat}
    {left right : TransitionDescription}
    (hleft : left ∈ validatorBlockLogicalRows D logical)
    (hright : right ∈ validatorBlockLogicalRows D logical)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  rcases validatorBlockLogicalRows_cases hleft with
    hleftDecoder | ⟨leftRead, hleftLeaf⟩ | ⟨leftRead, hleftAction⟩
  · rcases validatorBlockLogicalRows_cases hright with
      hrightDecoder | ⟨rightRead, hrightLeaf⟩ |
        ⟨rightRead, hrightAction⟩
    · exact validatorBlockDecoderRows_deterministic
        hleftDecoder hrightDecoder hkey
    · have hleftRange := validatorBlockDecoderRows_source_range hleftDecoder
      have hrightKey := validatorBlockLeafRows_key hrightLeaf
      have hrightRange := validatorBlockLeafState_range logical rightRead
      have hsource := hkey.1
      rw [hrightKey.1] at hsource
      lia
    · have hleftRange := validatorBlockDecoderRows_source_range hleftDecoder
      have hrightRange := validatorBlockActionRows_source_range hrightAction
      have hsource := hkey.1
      lia
  · rcases validatorBlockLogicalRows_cases hright with
      hrightDecoder | ⟨rightRead, hrightLeaf⟩ |
        ⟨rightRead, hrightAction⟩
    · have hleftKey := validatorBlockLeafRows_key hleftLeaf
      have hleftRange := validatorBlockLeafState_range logical leftRead
      have hrightRange := validatorBlockDecoderRows_source_range hrightDecoder
      have hsource := hkey.1
      rw [hleftKey.1] at hsource
      lia
    · have hleftKey := validatorBlockLeafRows_key hleftLeaf
      have hrightKey := validatorBlockLeafRows_key hrightLeaf
      have hstate : validatorBlockLeafState logical leftRead =
          validatorBlockLeafState logical rightRead := by
        rw [← hleftKey.1, ← hrightKey.1]
        exact hkey.1
      have hfourth : leftRead.fourthBit = rightRead.fourthBit := by
        have hread := hkey.2
        rw [hleftKey.2.1, hrightKey.2.1] at hread
        exact Option.some.inj hread
      have hsymbol := validatorBlockSymbol_eq_of_leaf_key hstate hfourth
      subst rightRead
      have hrowEq := validatorBlockLeafRows_eq_of_mem
        hleftLeaf hrightLeaf
      subst right
      exact ⟨rfl, rfl, rfl⟩
    · have hleftKey := validatorBlockLeafRows_key hleftLeaf
      have hleftRange := validatorBlockLeafState_range logical leftRead
      have hrightRange := validatorBlockActionRows_source_range hrightAction
      have hsource := hkey.1
      rw [hleftKey.1] at hsource
      lia
  · rcases validatorBlockLogicalRows_cases hright with
      hrightDecoder | ⟨rightRead, hrightLeaf⟩ |
        ⟨rightRead, hrightAction⟩
    · have hleftRange := validatorBlockActionRows_source_range hleftAction
      have hrightRange := validatorBlockDecoderRows_source_range hrightDecoder
      have hsource := hkey.1
      lia
    · have hleftRange := validatorBlockActionRows_source_range hleftAction
      have hrightKey := validatorBlockLeafRows_key hrightLeaf
      have hrightRange := validatorBlockLeafState_range logical rightRead
      have hsource := hkey.1
      rw [hrightKey.1] at hsource
      lia
    · have hleftRange :=
        validatorBlockActionRows_source_symbol_range hleftAction
      have hrightRange :=
        validatorBlockActionRows_source_symbol_range hrightAction
      have hrightRange' :
          validatorBlockActionState logical rightRead 0 ≤ left.source ∧
            left.source <
              validatorBlockActionState logical rightRead 0 + 7 := by
        rw [hkey.1]
        exact hrightRange
      have hsymbol := validatorBlockSymbol_eq_of_action_ranges
        hleftRange hrightRange'
      subst rightRead
      exact validatorBlockActionRows_deterministic
        hleftAction hrightAction hkey

/-- The generated physical block compiler is deterministic by construction;
the proof follows its disjoint decoder, leaf, and action-state regions. -/
theorem compileValidatorBlockDescription_deterministic
    (D : ValidatorBlockDescription) :
    (compileValidatorBlockDescription D).Deterministic := by
  intro left right hleft hright hkey
  rcases compiledRow_mem_logicalRows hleft with
    ⟨leftOwner, _hleftOwner, hleftRow⟩
  rcases compiledRow_mem_logicalRows hright with
    ⟨rightOwner, _hrightOwner, hrightRow⟩
  have hleftRange := validatorBlockLogicalRows_source_range hleftRow
  have hrightRange := validatorBlockLogicalRows_source_range hrightRow
  have hrightRange' :
      validatorBlockRootState rightOwner ≤ left.source ∧
        left.source <
          validatorBlockRootState rightOwner + validatorBlockStateWidth := by
    rw [hkey.1]
    exact hrightRange
  have howner := validatorBlockLogical_eq_of_ranges
    hleftRange hrightRange'
  subst rightOwner
  exact validatorBlockLogicalRows_deterministic hleftRow hrightRow hkey

/-- Every generated row source lies below the compiled physical state count. -/
theorem compileValidatorBlockDescription_source_lt
    (D : ValidatorBlockDescription) (row : TransitionDescription)
    (hrow : row ∈ (compileValidatorBlockDescription D).transitions) :
    row.source < (compileValidatorBlockDescription D).stateCount := by
  rcases compiledRow_mem_logicalRows hrow with
    ⟨logical, hlogical, hlogicalRow⟩
  have hrange := validatorBlockLogicalRows_source_range hlogicalRow
  simp [compileValidatorBlockDescription, validatorBlockRootState,
    validatorBlockStateWidth] at hrange ⊢
  lia

private theorem validatorFourLeftEntryRows_source_ge
    {core : MachineDescription} {row : TransitionDescription}
    (hrow : row ∈ validatorFourLeftEntryRows core) :
    core.stateCount ≤ row.source := by
  simp only [validatorFourLeftEntryRows, List.mem_append,
    validatorFourLeftEntryRowsAt, List.mem_cons, List.not_mem_nil,
    or_false] at hrow
  rcases hrow with
    (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl)
  all_goals
    simp [validatorFourLeftEntryRow, validatorFourLeftEntryState] <;>
    lia

private theorem validatorFourLeftEntryRows_deterministic
    {core : MachineDescription} {left right : TransitionDescription}
    (hleft : left ∈ validatorFourLeftEntryRows core)
    (hright : right ∈ validatorFourLeftEntryRows core)
    (hkey : TransitionDescription.SameKey left right) :
    TransitionDescription.SameAction left right := by
  simp only [validatorFourLeftEntryRows, List.mem_append,
    validatorFourLeftEntryRowsAt, List.mem_cons, List.not_mem_nil,
    or_false] at hleft hright
  rcases hleft with
    (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;>
  rcases hright with
    (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;>
  simp_all [TransitionDescription.SameKey,
    TransitionDescription.SameAction, validatorFourLeftEntryRow,
    validatorFourLeftEntryState] <;>
  lia

/-- The shared four-left wrapper preserves determinism when all core row
sources lie below the wrapper's fresh state block. -/
theorem withValidatorFourLeftEntry_deterministic
    (core : MachineDescription)
    (hsource : forall row : TransitionDescription,
      row ∈ core.transitions -> row.source < core.stateCount)
    (hdet : core.Deterministic) :
    (withValidatorFourLeftEntry core).Deterministic := by
  intro left right hleft hright hkey
  simp only [withValidatorFourLeftEntry, List.mem_append] at hleft hright
  rcases hleft with hleftCore | hleftEntry
  · rcases hright with hrightCore | hrightEntry
    · exact hdet left right hleftCore hrightCore hkey
    · have hlt := hsource left hleftCore
      have hge := validatorFourLeftEntryRows_source_ge hrightEntry
      have hsources := hkey.1
      lia
  · rcases hright with hrightCore | hrightEntry
    · have hge := validatorFourLeftEntryRows_source_ge hleftEntry
      have hlt := hsource right hrightCore
      have hsources := hkey.1
      lia
    · exact validatorFourLeftEntryRows_deterministic
        hleftEntry hrightEntry hkey

/-- Determinism certificate for a generated block compiler with the shared
four-cell entry wrapper. -/
theorem withValidatorFourLeftEntry_compileValidatorBlockDescription_deterministic
    (D : ValidatorBlockDescription) :
    (withValidatorFourLeftEntry
      (compileValidatorBlockDescription D)).Deterministic := by
  exact withValidatorFourLeftEntry_deterministic
    (compileValidatorBlockDescription D)
    (compileValidatorBlockDescription_source_lt D)
    (compileValidatorBlockDescription_deterministic D)

private theorem validatorBlockRootState_lt_physicalStateCount
    {stateCount logical : Nat} (hlogical : logical < stateCount) :
    validatorBlockRootState logical <
      stateCount * validatorBlockStateWidth := by
  simp [validatorBlockRootState, validatorBlockStateWidth] at *
  lia

private theorem validatorBlockLeafState_lt_physicalStateCount
    {stateCount logical : Nat} (read : ValidatorBlockSymbol)
    (hlogical : logical < stateCount) :
    validatorBlockLeafState logical read <
      stateCount * validatorBlockStateWidth := by
  cases read <;>
    simp [validatorBlockLeafState, validatorBlockDecode3State,
      validatorBlockRootState, validatorBlockBoolCode,
      validatorBlockStateWidth, ValidatorBlockSymbol.firstBit,
      ValidatorBlockSymbol.secondBit,
      ValidatorBlockSymbol.thirdBit] at * <;>
    lia

private theorem validatorBlockActionState_lt_physicalStateCount
    {stateCount logical : Nat} (read : ValidatorBlockSymbol)
    (phase : Nat) (hlogical : logical < stateCount)
    (hphase : phase < 7) :
    validatorBlockActionState logical read phase <
      stateCount * validatorBlockStateWidth := by
  have hrange := validatorBlockActionState_range
    logical read phase hphase
  have hroot := validatorBlockRootState_lt_physicalStateCount hlogical
  simp [validatorBlockRootState, validatorBlockStateWidth] at hrange hroot ⊢
  lia

private theorem validatorBlockDecoderRows_wellFormed
    {stateCount logical : Nat} {physicalRow : TransitionDescription}
    (hlogical : logical < stateCount)
    (hmem : physicalRow ∈ validatorBlockDecoderRows logical) :
    TransitionDescription.WellFormed
      (stateCount * validatorBlockStateWidth) physicalRow := by
  simp only [validatorBlockDecoderRows, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [TransitionDescription.WellFormed,
      validatorKeepPhysicalRow, validatorPhysicalRow,
      validatorBlockDecode1State, validatorBlockDecode2State,
      validatorBlockDecode3State, validatorBlockRootState,
      validatorBlockBoolCode, validatorBlockStateWidth] at * <;>
    lia

private theorem validatorBlockActionPair_wellFormed
    {stateCount logical : Nat} (read : ValidatorBlockSymbol)
    (sourcePhase targetPhase : Nat) (hlogical : logical < stateCount)
    (hsource : sourcePhase < 7) (htarget : targetPhase < 7) :
    validatorBlockActionState logical read sourcePhase <
        stateCount * validatorBlockStateWidth ∧
      validatorBlockActionState logical read targetPhase <
        stateCount * validatorBlockStateWidth :=
  ⟨validatorBlockActionState_lt_physicalStateCount
      read sourcePhase hlogical hsource,
    validatorBlockActionState_lt_physicalStateCount
      read targetPhase hlogical htarget⟩

private theorem validatorBlockActionRoot_wellFormed
    {stateCount logical target : Nat} (read : ValidatorBlockSymbol)
    (phase : Nat) (hlogical : logical < stateCount)
    (htarget : target < stateCount) (hphase : phase < 7) :
    validatorBlockActionState logical read phase <
        stateCount * validatorBlockStateWidth ∧
      validatorBlockRootState target <
        stateCount * validatorBlockStateWidth :=
  ⟨validatorBlockActionState_lt_physicalStateCount
      read phase hlogical hphase,
    validatorBlockRootState_lt_physicalStateCount htarget⟩

private theorem validatorBlockRightFlipRows_wellFormed
    {stateCount logical target : Nat}
    {read write : ValidatorBlockSymbol}
    {physicalRow : TransitionDescription}
    (hlogical : logical < stateCount) (htarget : target < stateCount)
    (hmem : physicalRow ∈
      validatorBlockRightFlipRows logical read write target) :
    TransitionDescription.WellFormed
      (stateCount * validatorBlockStateWidth) physicalRow := by
  simp only [validatorBlockRightFlipRows, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact validatorBlockActionPair_wellFormed
      read 0 1 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 1 2 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 2 3 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 3 4 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 4 5 hlogical (by decide) (by decide)
  · exact validatorBlockActionRoot_wellFormed
      read 5 hlogical htarget (by decide)

private theorem validatorBlockLeftRows_wellFormed
    {stateCount logical target : Nat}
    {read write : ValidatorBlockSymbol}
    {physicalRow : TransitionDescription}
    (hlogical : logical < stateCount) (htarget : target < stateCount)
    (hmem : physicalRow ∈ validatorBlockLeftRows logical read write target) :
    TransitionDescription.WellFormed
      (stateCount * validatorBlockStateWidth) physicalRow := by
  simp only [validatorBlockLeftRows, validatorKeepEitherRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    (((((rfl | rfl | rfl) | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | rfl
  · exact validatorBlockActionPair_wellFormed
      read 0 1 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 1 2 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 2 3 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 3 6 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 3 4 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 3 4 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 4 5 hlogical (by decide) (by decide)
  · exact validatorBlockActionPair_wellFormed
      read 4 5 hlogical (by decide) (by decide)
  · exact validatorBlockActionRoot_wellFormed
      read 5 hlogical htarget (by decide)
  · exact validatorBlockActionRoot_wellFormed
      read 5 hlogical htarget (by decide)
  · exact validatorBlockActionRoot_wellFormed
      read 6 hlogical htarget (by decide)

private theorem validatorBlockLeafRows_wellFormed
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {physicalRow : TransitionDescription}
    (hlogical : logical < D.stateCount)
    (htarget : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.target < D.stateCount)
    (hmem : physicalRow ∈ validatorBlockLeafRows D logical read) :
    TransitionDescription.WellFormed
      (D.stateCount * validatorBlockStateWidth) physicalRow := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockLeafRows, hlookup] at hmem
  | some row =>
      have hrowTarget := htarget row
        (ValidatorBlockDescription.lookup_mem hlookup)
      by_cases htail : row.read.tailBits = row.write.tailBits
      · by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · have hphysical : physicalRow =
                validatorKeepPhysicalRow
                  (validatorBlockDecode3State logical
                    read.firstBit read.secondBit read.thirdBit)
                  read.fourthBit Direction.right
                  (validatorBlockRootState row.target) := by
              simpa [validatorBlockLeafRows, hlookup, htail, hmove,
                hfirst] using hmem
            subst physicalRow
            exact ⟨
              validatorBlockLeafState_lt_physicalStateCount
                read hlogical,
              validatorBlockRootState_lt_physicalStateCount hrowTarget⟩
          · have hphysical : physicalRow =
                validatorKeepPhysicalRow
                  (validatorBlockDecode3State logical
                    read.firstBit read.secondBit read.thirdBit)
                  read.fourthBit Direction.left
                  (validatorBlockActionState logical read 0) := by
              simpa [validatorBlockLeafRows, hlookup, htail, hmove,
                hfirst] using hmem
            subst physicalRow
            exact ⟨
              validatorBlockLeafState_lt_physicalStateCount
                read hlogical,
              validatorBlockActionState_lt_physicalStateCount
                read 0 hlogical (by decide)⟩
        · have hphysical : physicalRow =
              validatorKeepPhysicalRow
                (validatorBlockDecode3State logical
                  read.firstBit read.secondBit read.thirdBit)
                read.fourthBit Direction.left
                (validatorBlockActionState logical read 0) := by
            simpa [validatorBlockLeafRows, hlookup, htail, hmove]
              using hmem
          subst physicalRow
          exact ⟨
            validatorBlockLeafState_lt_physicalStateCount read hlogical,
            validatorBlockActionState_lt_physicalStateCount
              read 0 hlogical (by decide)⟩
      · simp [validatorBlockLeafRows, hlookup, htail] at hmem

private theorem validatorBlockActionRows_wellFormed
    {D : ValidatorBlockDescription} {logical : Nat}
    {read : ValidatorBlockSymbol} {physicalRow : TransitionDescription}
    (hlogical : logical < D.stateCount)
    (htarget : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.target < D.stateCount)
    (hmem : physicalRow ∈ validatorBlockActionRows D logical read) :
    TransitionDescription.WellFormed
      (D.stateCount * validatorBlockStateWidth) physicalRow := by
  cases hlookup : D.lookup logical read with
  | none =>
      simp [validatorBlockActionRows, hlookup] at hmem
  | some row =>
      have hrowTarget := htarget row
        (ValidatorBlockDescription.lookup_mem hlookup)
      have hreadEq := (ValidatorBlockDescription.lookup_matches hlookup).2
      by_cases htail : row.read.tailBits = row.write.tailBits
      · have htailRead : read.tailBits = row.write.tailBits := by
          rw [← hreadEq]
          exact htail
        by_cases hmove : row.move = Direction.right
        · by_cases hfirst : row.read.firstBit = row.write.firstBit
          · simp [validatorBlockActionRows, hlookup, htail, hmove,
              hfirst] at hmem
          · have hfirstRead : read.firstBit ≠ row.write.firstBit := by
              rw [← hreadEq]
              exact hfirst
            exact validatorBlockRightFlipRows_wellFormed
              hlogical hrowTarget
              (by simpa [validatorBlockActionRows, hlookup, htail,
                hmove, hfirst, hreadEq, htailRead, hfirstRead]
                using hmem)
        · exact validatorBlockLeftRows_wellFormed
            hlogical hrowTarget
            (by simpa [validatorBlockActionRows, hlookup, htail,
              hmove, hreadEq, htailRead] using hmem)
      · simp [validatorBlockActionRows, hlookup, htail] at hmem

private theorem validatorBlockLogicalRows_wellFormed
    {D : ValidatorBlockDescription} {logical : Nat}
    {physicalRow : TransitionDescription}
    (hlogical : logical < D.stateCount)
    (htarget : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.target < D.stateCount)
    (hmem : physicalRow ∈ validatorBlockLogicalRows D logical) :
    TransitionDescription.WellFormed
      (D.stateCount * validatorBlockStateWidth) physicalRow := by
  rcases validatorBlockLogicalRows_cases hmem with
    hdecoder | ⟨read, hleaf⟩ | ⟨read, haction⟩
  · exact validatorBlockDecoderRows_wellFormed hlogical hdecoder
  · exact validatorBlockLeafRows_wellFormed hlogical htarget hleaf
  · exact validatorBlockActionRows_wellFormed hlogical htarget haction

/-- Generated physical endpoints are in range whenever every logical target
is in the declared logical state range. -/
theorem compileValidatorBlockDescription_transition_wellFormed
    (D : ValidatorBlockDescription)
    (htarget : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.target < D.stateCount)
    (physicalRow : TransitionDescription)
    (hmem : physicalRow ∈
      (compileValidatorBlockDescription D).transitions) :
    TransitionDescription.WellFormed
      (compileValidatorBlockDescription D).stateCount physicalRow := by
  rcases compiledRow_mem_logicalRows hmem with
    ⟨logical, hlogical, hlogicalRow⟩
  exact validatorBlockLogicalRows_wellFormed
    hlogical htarget hlogicalRow

private theorem validatorFourLeftEntryRows_wellFormed
    {core : MachineDescription} {physicalRow : TransitionDescription}
    (hstart : core.start < core.stateCount)
    (hmem : physicalRow ∈ validatorFourLeftEntryRows core) :
    TransitionDescription.WellFormed
      (core.stateCount + 4) physicalRow := by
  simp only [validatorFourLeftEntryRows, List.mem_append,
    validatorFourLeftEntryRowsAt, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with
    (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl)
  all_goals
    simp [TransitionDescription.WellFormed,
      validatorFourLeftEntryRow, validatorFourLeftEntryState] at * <;>
    lia

private theorem withValidatorFourLeftEntry_transition_wellFormed
    (core : MachineDescription)
    (hstart : core.start < core.stateCount)
    (hcore : forall row : TransitionDescription,
      row ∈ core.transitions ->
        TransitionDescription.WellFormed core.stateCount row)
    (physicalRow : TransitionDescription)
    (hmem : physicalRow ∈
      (withValidatorFourLeftEntry core).transitions) :
    TransitionDescription.WellFormed
      (withValidatorFourLeftEntry core).stateCount physicalRow := by
  simp only [withValidatorFourLeftEntry, List.mem_append] at hmem ⊢
  rcases hmem with hcoreRow | hentryRow
  · have hwell := hcore physicalRow hcoreRow
    exact ⟨Nat.lt_trans hwell.1 (by lia),
      Nat.lt_trans hwell.2 (by lia)⟩
  · exact validatorFourLeftEntryRows_wellFormed hstart hentryRow

/-- The entry-wrapped generated compiler is well formed from the three small
logical state-bound obligations. -/
theorem withValidatorFourLeftEntry_compileValidatorBlockDescription_wellFormed
    (D : ValidatorBlockDescription)
    (hstart : D.start < D.stateCount)
    (hhalt : D.halt < D.stateCount)
    (htarget : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.target < D.stateCount) :
    (withValidatorFourLeftEntry
      (compileValidatorBlockDescription D)).WellFormed := by
  let core := compileValidatorBlockDescription D
  have hcoreStart : core.start < core.stateCount := by
    exact validatorBlockRootState_lt_physicalStateCount hstart
  have hcoreHalt : core.halt < core.stateCount := by
    exact validatorBlockRootState_lt_physicalStateCount hhalt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [withValidatorFourLeftEntry]
  · simp [withValidatorFourLeftEntry, validatorFourLeftEntryState]
  · change core.halt < core.stateCount + 4
    exact Nat.lt_trans hcoreHalt (by lia)
  · exact withValidatorFourLeftEntry_transition_wellFormed
      core hcoreStart
      (compileValidatorBlockDescription_transition_wellFormed D htarget)
  · exact
      withValidatorFourLeftEntry_compileValidatorBlockDescription_deterministic
        D

/-- Generated block rows never leave the compiled logical halt state. -/
theorem compileValidatorBlockDescription_haltTransitionFree
    (D : ValidatorBlockDescription) :
    (compileValidatorBlockDescription D).HaltTransitionFree := by
  intro physicalRow hmem hsource
  rcases compiledRow_mem_logicalRows hmem with
    ⟨logical, _hlogical, hlogicalRow⟩
  have hnotHalt : logical ≠ D.halt := by
    intro hlogicalHalt
    subst logical
    simp [validatorBlockLogicalRows] at hlogicalRow
  have hrange := validatorBlockLogicalRows_source_range hlogicalRow
  have hsourceRoot :
      physicalRow.source = validatorBlockRootState D.halt := by
    simpa using hsource
  rw [hsourceRoot] at hrange
  have hlogicalHalt : logical = D.halt := by
    simp [validatorBlockRootState, validatorBlockStateWidth] at hrange
    lia
  exact hnotHalt hlogicalHalt

private theorem withValidatorFourLeftEntry_haltTransitionFree
    (core : MachineDescription) (hhalt : core.halt < core.stateCount)
    (hcore : core.HaltTransitionFree) :
    (withValidatorFourLeftEntry core).HaltTransitionFree := by
  intro physicalRow hmem hsource
  simp only [withValidatorFourLeftEntry, List.mem_append] at hmem
  rcases hmem with hcoreRow | hentryRow
  · exact hcore physicalRow hcoreRow (by
      simpa [withValidatorFourLeftEntry] using hsource)
  · have hentrySource :=
      validatorFourLeftEntryRows_source_ge hentryRow
    have hsourceCore : physicalRow.source = core.halt := by
      simpa [withValidatorFourLeftEntry] using hsource
    lia

/-- The shared entry wrapper preserves the generated compiler's absence of
outgoing halt-state rows. -/
theorem withValidatorFourLeftEntry_compileValidatorBlockDescription_haltTransitionFree
    (D : ValidatorBlockDescription) (hhalt : D.halt < D.stateCount) :
    (withValidatorFourLeftEntry
      (compileValidatorBlockDescription D)).HaltTransitionFree := by
  apply withValidatorFourLeftEntry_haltTransitionFree
  · exact validatorBlockRootState_lt_physicalStateCount hhalt
  · exact compileValidatorBlockDescription_haltTransitionFree D

/-- Structural readiness certificate for the shared entry wrapper around a
generated Boolean block compiler. -/
theorem withValidatorFourLeftEntry_compileValidatorBlockDescription_subroutineReady
    (D : ValidatorBlockDescription)
    (hstart : D.start < D.stateCount)
    (hhalt : D.halt < D.stateCount)
    (htarget : forall row : ValidatorBlockTransition,
      row ∈ D.transitions -> row.target < D.stateCount) :
    (withValidatorFourLeftEntry
      (compileValidatorBlockDescription D)).SubroutineReady := by
  exact ⟨
    withValidatorFourLeftEntry_compileValidatorBlockDescription_wellFormed
      D hstart hhalt htarget,
    withValidatorFourLeftEntry_compileValidatorBlockDescription_haltTransitionFree
      D hhalt⟩

end SelfHaltingRecognizer
end Computability
end FoC

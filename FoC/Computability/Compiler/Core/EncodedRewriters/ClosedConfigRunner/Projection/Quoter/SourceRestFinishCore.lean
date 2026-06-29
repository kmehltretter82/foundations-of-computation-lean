import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.ScanRightToBlankLeft

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def assemblySourceRestFinishSourceBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (List.append
      (DovetailInitialLayoutInitializer.stageInputBits w stage)
      sourceRestBits)

def assemblySourceRestFinishSourcePrefixBits
    (w : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (DovetailInitialLayoutInitializer.stageInputBits w stage)

def assemblySourceRestFinishTargetPrefixBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.header)
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
      (preservingCellPassCellBits
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)))

theorem assemblySourceRestFinishSourceBits_eq
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSourceBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits w stage)
          sourceRestBits) := by
  rfl

theorem assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSourceBits w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        sourceRestBits := by
  simp [assemblySourceRestFinishSourceBits,
    assemblySourceRestFinishSourcePrefixBits, List.append_assoc]

theorem assemblySourceRestFinishSourceBits_length_eq_prefix_add
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishSourceBits w sourceRestBits stage).length =
      (assemblySourceRestFinishSourcePrefixBits w stage).length +
        sourceRestBits.length := by
  rw [assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  simp

theorem assemblySourceRestFinishSourceBits_headerPrefix
    (w sourceRestBits : Word Bool) (stage : Nat) :
    exists rest : Word Bool,
      assemblySourceRestFinishSourceBits w sourceRestBits stage =
        false :: false :: false :: true :: rest := by
  refine
    ⟨List.append
      (DovetailInitialLayoutInitializer.stageInputBits w stage)
      sourceRestBits, ?_⟩
  simp [assemblySourceRestFinishSourceBits, encodeCodeSymbolAsInput]

theorem assemblySourceRestFinishSourceBits_length_ge_header
    (w sourceRestBits : Word Bool) (stage : Nat) :
    4 <= (assemblySourceRestFinishSourceBits w sourceRestBits stage).length := by
  rw [assemblySourceRestFinishSourceBits_eq]
  simp [encodeCodeSymbolAsInput]

theorem assemblySourceRestFinishTargetPrefixBits_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
          (preservingCellPassCellBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage))) := by
  rfl

theorem assemblySourceRestFinishTargetPrefixBits_eq_encodeBoolWordAppend
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (assemblySourceRestFinishSourceBits w sourceRestBits stage)
            []) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote]
  exact
    preservingCellPassHeaderQuoteBits_eq_encodeBoolWordAppend
      (assemblySourceRestFinishSourceBits w sourceRestBits stage)

theorem preservingCellPassCellBits_append_bool
    (pref suffix : Word Bool) :
    preservingCellPassCellBits (List.append pref suffix) =
      List.append (preservingCellPassCellBits pref)
        (preservingCellPassCellBits suffix) := by
  induction pref with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b
      · simp [preservingCellPassCellBits, preservingCellPassZeroBits]
        change
          false :: true :: false :: true ::
              preservingCellPassCellBits (List.append rest suffix) =
            false :: true :: false :: true ::
              List.append (preservingCellPassCellBits rest)
                (preservingCellPassCellBits suffix)
        rw [ih]
      · simp [preservingCellPassCellBits, preservingCellPassOneBits]
        change
          false :: true :: true :: false ::
              preservingCellPassCellBits (List.append rest suffix) =
            false :: true :: true :: false ::
              List.append (preservingCellPassCellBits rest)
                (preservingCellPassCellBits suffix)
        rw [ih]

theorem assemblySourceRestFinishTargetPrefixBits_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourcePrefixBits w stage))
            (preservingCellPassCellBits sourceRestBits))) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest,
    preservingCellPassCellBits_append_bool]

theorem assemblySourceRestFinishTargetPrefixBits_length_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage).length =
      4 +
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (assemblySourceRestFinishSourceBits w sourceRestBits stage).length).length +
        4 * (assemblySourceRestFinishSourceBits w sourceRestBits stage).length := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote]
  simp [encodeCodeSymbolAsInput, preservingCellPassCellBits_length]
  omega

theorem assemblySourceRestFinishTargetPrefixBits_length_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage).length =
      4 +
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (assemblySourceRestFinishSourceBits w sourceRestBits stage).length).length +
        4 * (assemblySourceRestFinishSourcePrefixBits w stage).length +
        4 * sourceRestBits.length := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote]
  simp [encodeCodeSymbolAsInput, preservingCellPassCellBits_length,
    Nat.add_assoc]
  omega

def assemblySourceRestFinishSourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    (none :: List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (List.append
      ((preservingCellPassCellBits sourceRestBits).map some)
      [none])

def assemblySourceRestFinishBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (none ::
      List.append
        ((preservingCellPassCellBits sourceRestBits).map some)
        [none])

def assemblySourceRestFinishTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((assemblySourceRestFinishTargetPrefixBits
      w sourceRestBits stage).reverse.map some)
    ((List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage)
      sourceRestBits).map some)

def AssemblySourceRestFinishSpec (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishSourceTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishSpec finish

def AssemblySourceRestFinishBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishBoundarySpec finish

def assemblySourceRestFinishLeftMoveDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1 ]

theorem assemblySourceRestFinishLeftMoveDescription_wellFormed :
    assemblySourceRestFinishLeftMoveDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := assemblySourceRestFinishLeftMoveDescription.transitions)
      (stateCount := assemblySourceRestFinishLeftMoveDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := assemblySourceRestFinishLeftMoveDescription.transitions)
      (by decide)

theorem assemblySourceRestFinishLeftMoveDescription_haltTransitionFree :
    assemblySourceRestFinishLeftMoveDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := assemblySourceRestFinishLeftMoveDescription.transitions)
    (state := assemblySourceRestFinishLeftMoveDescription.halt)
    (by decide)

theorem assemblySourceRestFinishLeftMoveDescription_subroutineReady :
    assemblySourceRestFinishLeftMoveDescription.SubroutineReady :=
  ⟨assemblySourceRestFinishLeftMoveDescription_wellFormed,
    assemblySourceRestFinishLeftMoveDescription_haltTransitionFree⟩

theorem assemblySourceRestFinishLeftMoveDescription_haltsFromTape
    (T : Tape Bool) :
    assemblySourceRestFinishLeftMoveDescription.HaltsFromTape T
      (Tape.move Direction.left T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [assemblySourceRestFinishLeftMoveDescription,
              runConfig, stepConfig, lookupTransition, Matches,
              transition, Tape.read, Tape.write, Tape.move]
        | some b =>
            cases b <;>
              simp [assemblySourceRestFinishLeftMoveDescription,
                runConfig, stepConfig, lookupTransition, Matches,
                transition, Tape.read, Tape.write, Tape.move]

theorem tapeAtCells_move_left_cons_append_singleton
    (left cells : List (Option Bool)) :
    Tape.move Direction.left
        (tapeAtCells (none :: left) (List.append cells [none])) =
      tapeAtCells left (none :: List.append cells [none]) := by
  cases cells <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft]

theorem tapeAtCells_move_left_move_right_none_cons_append_singleton
    (left cells : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells left (none :: List.append cells [none]))) =
      tapeAtCells left (none :: List.append cells [none]) := by
  cases cells <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySourceRestFinishSourceTape_move_left
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) =
      assemblySourceRestFinishBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishSourceTape,
    assemblySourceRestFinishBoundaryTape]
  exact
    tapeAtCells_move_left_cons_append_singleton
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      ((preservingCellPassCellBits sourceRestBits).map some)

theorem assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishLeftMoveDescription.HaltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) := by
  simpa [assemblySourceRestFinishSourceTape_move_left] using
    assemblySourceRestFinishLeftMoveDescription_haltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)

theorem assemblySourceRestFinishBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      assemblySourceRestFinishBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishBoundaryTape]
  exact
    tapeAtCells_move_left_move_right_none_cons_append_singleton
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      ((preservingCellPassCellBits sourceRestBits).map some)

def assemblySourceRestFinishQuoteBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanRightToBlankLeftHaltTape
    (none :: List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (preservingCellPassCellBits sourceRestBits)

def AssemblySourceRestFinishQuoteBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishQuoteBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishQuoteBoundarySpec finish

theorem scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishSourceTape,
    assemblySourceRestFinishQuoteBoundaryTape]
  exact
    scanRightToBlankLeftDescription_haltsFromTape
      (none :: List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)

theorem assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishQuoteBoundaryTape
            w sourceRestBits stage)) =
      assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage := by
  cases hquote : preservingCellPassCellBits sourceRestBits with
  | nil =>
      rw [assemblySourceRestFinishQuoteBoundaryTape, hquote]
      simp [scanRightToBlankLeftHaltTape, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons quoteHead quoteTail =>
      rw [assemblySourceRestFinishQuoteBoundaryTape, hquote]
      exact
        scanRightToBlankLeftHaltTape_move_left_move_right_cons
          (none :: List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
          quoteHead quoteTail

def assemblySourceRestFinishLeftBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanLeftToBlankLeftHaltTape
    (List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (preservingCellPassCellBits sourceRestBits)
    [none]

def AssemblySourceRestFinishLeftBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishLeftBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishLeftBoundarySpec finish

theorem scanLeftToBlankLeftDescription_haltsFrom_empty_scanRightToBlankLeftHaltTape
    (leftBase : List (Option Bool)) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (scanRightToBlankLeftHaltTape (none :: leftBase) [])
      (scanLeftToBlankLeftHaltTape leftBase [] [none]) := by
  refine ⟨1, ?_⟩
  constructor <;>
    simp [scanRightToBlankLeftHaltTape,
      scanLeftToBlankLeftHaltTape, scanLeftToBlankLeftDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

theorem scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
      (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) := by
  cases hquote : preservingCellPassCellBits sourceRestBits with
  | nil =>
      rw [assemblySourceRestFinishQuoteBoundaryTape,
        assemblySourceRestFinishLeftBoundaryTape, hquote]
      exact
        scanLeftToBlankLeftDescription_haltsFrom_empty_scanRightToBlankLeftHaltTape
          (List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
  | cons quoteHead quoteTail =>
      rcases exists_reverse_append_singleton_of_cons quoteHead quoteTail with
        ⟨scanRev, current, hscan⟩
      rw [assemblySourceRestFinishQuoteBoundaryTape,
        assemblySourceRestFinishLeftBoundaryTape, hquote, hscan]
      exact
        scanLeftToBlankLeftDescription_haltsFrom_scanRightToBlankLeftHaltTape
          (List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
          scanRev current

theorem assemblySourceRestFinishLeftBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_move_left_move_right_none_right
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)
      []

def assemblySourceRestFinishFromLeftBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanLeftToBlankLeftDescription finish

theorem assemblySourceRestFinishQuoteBoundarySpec_of_leftBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundarySpec finish) :
    AssemblySourceRestFinishQuoteBoundarySpec
      (assemblySourceRestFinishFromLeftBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
          w sourceRestBits stage)
        (assemblySourceRestFinishLeftBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    (h : AssemblySourceRestFinishLeftBoundaryConstruction) :
    AssemblySourceRestFinishQuoteBoundaryConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromLeftBoundary finish,
      assemblySourceRestFinishQuoteBoundarySpec_of_leftBoundary hfinish⟩

def assemblySourceRestFinishFromQuoteBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanRightToBlankLeftDescription finish

theorem assemblySourceRestFinishSpec_of_quoteBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundarySpec finish) :
    AssemblySourceRestFinishSpec
      (assemblySourceRestFinishFromQuoteBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishConstruction_of_quoteBoundary
    (h : AssemblySourceRestFinishQuoteBoundaryConstruction) :
    AssemblySourceRestFinishConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromQuoteBoundary finish,
      assemblySourceRestFinishSpec_of_quoteBoundary hfinish⟩

def assemblySourceRestFinishFromBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical assemblySourceRestFinishLeftMoveDescription finish

theorem assemblySourceRestFinishSpec_of_boundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundarySpec finish) :
    AssemblySourceRestFinishSpec
      (assemblySourceRestFinishFromBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.left
        (assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishConstruction_of_boundary
    (h : AssemblySourceRestFinishBoundaryConstruction) :
    AssemblySourceRestFinishConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromBoundary finish,
      assemblySourceRestFinishSpec_of_boundary hfinish⟩

theorem assemblySourceRestFinishLeftBoundaryConstruction :
    AssemblySourceRestFinishLeftBoundaryConstruction := by
  sorry

theorem assemblySourceRestFinishQuoteBoundaryConstruction :
    AssemblySourceRestFinishQuoteBoundaryConstruction :=
  assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    assemblySourceRestFinishLeftBoundaryConstruction

theorem assemblySourceRestFinishConstruction :
    AssemblySourceRestFinishConstruction :=
  assemblySourceRestFinishConstruction_of_quoteBoundary
    assemblySourceRestFinishQuoteBoundaryConstruction

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

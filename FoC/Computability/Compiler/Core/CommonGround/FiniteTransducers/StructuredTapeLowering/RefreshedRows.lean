import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.Rows
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTapeLowering.ActionSlack

set_option doc.verso true

/-!
# Refreshed structured row lowerings

This module extends the single-moving-tape row lowerer with an abstract guard
refresh normalizer.  Each local action may consume represented guard slack; the
refresh contract restores the canonical guarded encoding before the next
action begins.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering

private theorem list_eq_three_of_length_eq_three
    {α : Type} {xs : List α} (h : xs.length = 3) :
    exists a : α, exists b : α, exists c : α, xs = [a, b, c] := by
  cases xs with
  | nil =>
      simp at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp at h
      | cons b rest =>
          cases rest with
          | nil =>
              simp at h
          | cons c rest =>
              cases rest with
              | nil =>
                  exact ⟨a, b, c, rfl⟩
              | cons d rest =>
                  simp at h

/-!
## Refreshed action fragments
-/

def action0LocalMoveWithRefreshDescription
    (write? : Option (Option Bool)) (move : HeadMove)
    (refresh : MachineDescription) : MachineDescription :=
  guardedLogicalEquivThenRefreshDescription
    (action0LocalMoveDescription write? move)
    refresh

def action1LocalMoveWithRefreshDescription
    (write? : Option (Option Bool)) (move : HeadMove)
    (refresh : MachineDescription) : MachineDescription :=
  guardedLogicalEquivThenRefreshDescription
    (action1LocalMoveDescription write? move)
    refresh

def action2LocalMoveWithRefreshDescription
    (write? : Option (Option Bool)) (move : HeadMove)
    (refresh : MachineDescription) : MachineDescription :=
  guardedLogicalEquivThenRefreshDescription
    (action2LocalMoveDescription write? move)
    refresh

theorem action0LocalMoveWithRefreshDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (write? : Option (Option Bool)) (move : HeadMove)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (actionPrimitivesAt 0 { write? := write?, move := move })
      (action0LocalMoveWithRefreshDescription write? move refresh) := by
  simpa [action0LocalMoveWithRefreshDescription] using
    physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv_thenRefresh
      (action0LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write? move)
      hrefresh

theorem action1LocalMoveWithRefreshDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (write? : Option (Option Bool)) (move : HeadMove)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (actionPrimitivesAt 1 { write? := write?, move := move })
      (action1LocalMoveWithRefreshDescription write? move refresh) := by
  simpa [action1LocalMoveWithRefreshDescription] using
    physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv_thenRefresh
      (action1LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write? move)
      hrefresh

theorem action2LocalMoveWithRefreshDescription_physicalPrimitiveSequenceGuardedContractEquiv
    (write? : Option (Option Bool)) (move : HeadMove)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (actionPrimitivesAt 2 { write? := write?, move := move })
      (action2LocalMoveWithRefreshDescription write? move refresh) := by
  simpa [action2LocalMoveWithRefreshDescription] using
    physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv_thenRefresh
      (action2LocalMoveDescription_physicalPrimitiveSequenceGuardedLogicalEquivContractEquiv
        write? move)
      hrefresh

/-!
## Arbitrary local-move three-tape rows
-/

def readWriteMoveRow3DescriptionWithRefresh
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 move1 move2 : HeadMove)
    (refresh : MachineDescription) :
    MachineDescription :=
  canonicalPrimitiveSeqDescription
    (canonicalPrimitiveSeqDescription
      (canonicalPrimitiveSeqDescription
        (canonicalPrimitiveSeqDescription
          (canonicalPrimitiveSeqDescription
            (readCheck0Description read0)
            (readCheck1Description read1))
          (readCheck2Description read2))
        (action0LocalMoveWithRefreshDescription write0? move0 refresh))
      (action1LocalMoveWithRefreshDescription write1? move1 refresh))
    (action2LocalMoveWithRefreshDescription write2? move2 refresh)

theorem readWriteMoveRow3DescriptionWithRefresh_physicalPrimitiveSequenceGuardedContractEquiv
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 move1 move2 : HeadMove)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    PhysicalPrimitiveSequenceGuardedContractEquiv
      (transitionPrimitiveSequence3 read0 read1 read2
        { write? := write0?, move := move0 }
        { write? := write1?, move := move1 }
        { write? := write2?, move := move2 })
      (readWriteMoveRow3DescriptionWithRefresh read0 read1 read2
        write0? write1? write2? move0 move1 move2 refresh) := by
  have hread0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 0 read0)
        (readCheck0Description read0) :=
    readCheck0Description_physicalPrimitiveSequenceGuardedContractEquiv
      read0
  have hread1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 1 read1)
        (readCheck1Description read1) :=
    readCheck1Description_physicalPrimitiveSequenceGuardedContractEquiv
      read1
  have hread2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (readCheckPrimitivesAt 2 read2)
        (readCheck2Description read2) :=
    readCheck2Description_physicalPrimitiveSequenceGuardedContractEquiv
      read2
  have haction0 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 0
          { write? := write0?, move := move0 })
        (action0LocalMoveWithRefreshDescription
          write0? move0 refresh) :=
    action0LocalMoveWithRefreshDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write0? move0 hrefresh
  have haction1 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 1
          { write? := write1?, move := move1 })
        (action1LocalMoveWithRefreshDescription
          write1? move1 refresh) :=
    action1LocalMoveWithRefreshDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write1? move1 hrefresh
  have haction2 :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (actionPrimitivesAt 2
          { write? := write2?, move := move2 })
        (action2LocalMoveWithRefreshDescription
          write2? move2 refresh) :=
    action2LocalMoveWithRefreshDescription_physicalPrimitiveSequenceGuardedContractEquiv
      write2? move2 hrefresh
  have h01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      hread0 hread1
  have h012 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h01 hread2
  have h012a0 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012 haction0
  have h012a01 :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a0 haction1
  have hall :=
    physicalPrimitiveSequenceGuardedContractEquiv_append
      h012a01 haction2
  simpa [readWriteMoveRow3DescriptionWithRefresh,
    transitionPrimitiveSequence3, List.append_assoc] using hall

theorem readWriteMoveRow3DescriptionWithRefresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (read0 read1 read2 : Option Bool)
    (write0? write1? write2? : Option (Option Bool))
    (move0 move1 move2 : HeadMove)
    (hreads : t.reads = [read0, read1, read2])
    (hactions :
      t.actions =
        [ { write? := write0?, move := move0 }
        , { write? := write1?, move := move1 }
        , { write? := write2?, move := move2 } ])
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteMoveRow3DescriptionWithRefresh read0 read1 read2
        write0? write1? write2? move0 move1 move2 refresh) :=
  let action0 : TapeAction := { write? := write0?, move := move0 }
  let action1 : TapeAction := { write? := write1?, move := move1 }
  let action2 : TapeAction := { write? := write2?, move := move2 }
  have hsequence :
      PhysicalPrimitiveSequenceGuardedContractEquiv
        (transitionPrimitiveSequenceOfRow3 t)
        (readWriteMoveRow3DescriptionWithRefresh read0 read1 read2
          write0? write1? write2? move0 move1 move2 refresh) := by
    cases t with
    | mk source reads actions target =>
        simp [transitionPrimitiveSequenceOfRow3] at hreads hactions ⊢
        cases hreads
        cases hactions
        exact
          readWriteMoveRow3DescriptionWithRefresh_physicalPrimitiveSequenceGuardedContractEquiv
            read0 read1 read2 write0? write1? write2?
            move0 move1 move2 hrefresh
  guardedPrimitiveSequence3_lowersGuardedTransitionEquiv
    (hsequence := hsequence)
    hD read0 read1 read2 action0 action1 action2
    hreads hactions

def readWriteRow3DescriptionOfRowWithRefresh
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? move0
    , TapeAction.mk write1? move1
    , TapeAction.mk write2? move2 ] =>
      readWriteMoveRow3DescriptionWithRefresh read0 read1 read2
        write0? write1? write2? move0 move1 move2 refresh
  | _, _ => cursorNoopDescription

/--
Extract the chainable-slack row lowering machine directly from a transition
row.

This path supports arbitrary local moves on all three tapes without an abstract
guard refresh normalizer.  Its endpoint is only a logical-equivalence physical
tape, so callers that need the canonical guarded endpoint should use
{name}`readWriteRow3DescriptionOfRowWithRefresh`.
-/
def readActionSlackRow3DescriptionOfRow
    (t : Transition) : MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? move0
    , TapeAction.mk write1? move1
    , TapeAction.mk write2? move2 ] =>
      readActionSlackRow3Description read0 read1 read2
        write0? move0 write1? move1 write2? move2
  | _, _ => cursorNoopDescription

/--
Endpoint-aware refreshed row selector built from the chainable slack row.

This is the guard-slack-refresh successor to
{name}`readWriteRow3DescriptionOfRowWithRefresh`: it uses the row-produced
guard-slack endpoint contract rather than the broad logical-equivalence
refresh contract.
-/
def readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? move0
    , TapeAction.mk write1? move1
    , TapeAction.mk write2? move2 ] =>
      readActionSlackRow3DescriptionWithGuardSlackRefresh
        read0 read1 read2
        write0? move0 write1? move1 write2? move2
        refresh
  | _, _ => cursorNoopDescription

/--
Endpoint-aware refreshed row selector for the concrete row-produced singleton
shape contract.

This has the same physical shape as the guard-slack refreshed selector, but
the proof obligation on {lit}`refresh` is narrowed to the segment-wise
singleton endpoints that supported three-tape slack rows actually produce.
-/
def readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
    (t : Transition) (refresh : MachineDescription) :
    MachineDescription :=
  match t.reads, t.actions with
  | [read0, read1, read2],
    [ TapeAction.mk write0? move0
    , TapeAction.mk write1? move1
    , TapeAction.mk write2? move2 ] =>
      guardedLogicalEquivThenRefreshDescription
        (readActionSlackRow3Description read0 read1 read2
          write0? move0 write1? move1 write2? move2)
        refresh
  | _, _ => cursorNoopDescription

inductive SupportedReadWriteRow3
    (t : Transition) : Prop where
  | mk
      (read0 read1 read2 : Option Bool)
      (write0? write1? write2? : Option (Option Bool))
      (move0 move1 move2 : HeadMove)
      (hreads : t.reads = [read0, read1, read2])
      (hactions :
        t.actions =
          [ { write? := write0?, move := move0 }
          , { write? := write1?, move := move1 }
          , { write? := write2?, move := move2 } ]) :
      SupportedReadWriteRow3 t

def supportsReadWriteRow3
    (t : Transition) : Bool :=
  match t.reads, t.actions with
  | [_read0, _read1, _read2],
    [ TapeAction.mk _write0? _move0
    , TapeAction.mk _write1? _move1
    , TapeAction.mk _write2? _move2 ] => true
  | _, _ => false

theorem supportsReadWriteRow3_eq_true_of_supported
    {t : Transition}
    (h : SupportedReadWriteRow3 t) :
    supportsReadWriteRow3 t = true := by
  cases h with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [supportsReadWriteRow3] at hreads hactions ⊢
          cases hreads
          cases hactions
          rfl

theorem supportedReadWriteRow3_of_supports_eq_true
    {t : Transition}
    (h : supportsReadWriteRow3 t = true) :
    SupportedReadWriteRow3 t := by
  cases t with
  | mk source reads actions target =>
      cases reads with
      | nil =>
          simp [supportsReadWriteRow3] at h
      | cons read0 reads1 =>
          cases reads1 with
          | nil =>
              simp [supportsReadWriteRow3] at h
          | cons read1 reads2 =>
              cases reads2 with
              | nil =>
                  simp [supportsReadWriteRow3] at h
              | cons read2 reads3 =>
                  cases reads3 with
                  | nil =>
                      cases actions with
                      | nil =>
                          simp [supportsReadWriteRow3] at h
                      | cons action0 actions1 =>
                          cases action0 with
                          | mk write0? move0 =>
                              cases actions1 with
                              | nil =>
                                  simp [supportsReadWriteRow3] at h
                              | cons action1 actions2 =>
                                  cases action1 with
                                  | mk write1? move1 =>
                                      cases actions2 with
                                      | nil =>
                                          simp [supportsReadWriteRow3] at h
                                      | cons action2 actions3 =>
                                          cases action2 with
                                          | mk write2? move2 =>
                                              cases actions3 with
                                              | nil =>
                                                  exact
                                                    SupportedReadWriteRow3.mk
                                                      read0 read1 read2
                                                      write0? write1?
                                                      write2? move0 move1
                                                      move2 rfl rfl
                                              | cons _ _ =>
                                                  simp [supportsReadWriteRow3]
                                                    at h
                  | cons _ _ =>
                      simp [supportsReadWriteRow3] at h

theorem supportsReadWriteRow3_eq_true_iff
    (t : Transition) :
    supportsReadWriteRow3 t = true ↔
      SupportedReadWriteRow3 t :=
  ⟨supportedReadWriteRow3_of_supports_eq_true,
    supportsReadWriteRow3_eq_true_of_supported⟩

theorem readWriteRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedReadWriteRow3 t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteRow3DescriptionOfRowWithRefresh t refresh) := by
  cases hsupported with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [readWriteRow3DescriptionOfRowWithRefresh]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readWriteMoveRow3DescriptionWithRefresh_lowersGuardedTransitionEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := move0 }
                  , { write? := write1?, move := move1 }
                  , { write? := write2?, move := move2 } ]
                target := target }
              hD read0 read1 read2 write0? write1? write2?
              move0 move1 move2 rfl rfl hrefresh

theorem readWriteRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsReadWriteRow3 t = true)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteRow3DescriptionOfRowWithRefresh t refresh) :=
  readWriteRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv
    D t hD
    (supportedReadWriteRow3_of_supports_eq_true hsupported)
    hrefresh

theorem readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedReadWriteRow3 t) :
    LowersGuardedTransitionLogicalEquiv D t
      (readActionSlackRow3DescriptionOfRow t) := by
  cases hsupported with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [readActionSlackRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readActionSlackRow3Description_lowersGuardedTransitionLogicalEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := move0 }
                  , { write? := write1?, move := move1 }
                  , { write? := write2?, move := move2 } ]
                target := target }
              hD read0 read1 read2 write0? move0 write1?
              move1 write2? move2 rfl rfl

theorem readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsReadWriteRow3 t = true) :
    LowersGuardedTransitionLogicalEquiv D t
      (readActionSlackRow3DescriptionOfRow t) :=
  readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv
    D t hD
    (supportedReadWriteRow3_of_supports_eq_true hsupported)

theorem readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionGuardSlack
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedReadWriteRow3 t) :
    LowersGuardedTransitionGuardSlack D t
      (readActionSlackRow3DescriptionOfRow t) := by
  cases hsupported with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [readActionSlackRow3DescriptionOfRow]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readActionSlackRow3Description_lowersGuardedTransitionGuardSlack
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := move0 }
                  , { write? := write1?, move := move1 }
                  , { write? := write2?, move := move2 } ]
                target := target }
              hD read0 read1 read2 write0? move0 write1?
              move1 write2? move2 rfl rfl

theorem readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionGuardSlack_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsReadWriteRow3 t = true) :
    LowersGuardedTransitionGuardSlack D t
      (readActionSlackRow3DescriptionOfRow t) :=
  readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionGuardSlack
    D t hD
    (supportedReadWriteRow3_of_supports_eq_true hsupported)

theorem readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedReadWriteRow3 t)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh) := by
  cases hsupported with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          exact
            readActionSlackRow3DescriptionWithGuardSlackRefresh_lowersGuardedTransitionEquiv
              D
              { source := source
                reads := [read0, read1, read2]
                actions :=
                  [ { write? := write0?, move := move0 }
                  , { write? := write1?, move := move1 }
                  , { write? := write2?, move := move2 } ]
                target := target }
              hD read0 read1 read2 write0? move0 write1?
              move1 write2? move2 rfl rfl hrefresh

theorem readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh_lowersGuardedTransitionEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsReadWriteRow3 t = true)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh) :=
  readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh_lowersGuardedTransitionEquiv
    D t hD
    (supportedReadWriteRow3_of_supports_eq_true hsupported)
    hrefresh

theorem readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedReadWriteRow3 t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) := by
  cases hsupported with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          let row :=
            readActionSlackRow3Description read0 read1 read2
              write0? move0 write1? move1 write2? move2
          let transition : Transition :=
            { source := source
              reads := [read0, read1, read2]
              actions :=
                [ { write? := write0?, move := move0 }
                , { write? := write1?, move := move1 }
                , { write? := write2?, move := move2 } ]
              target := target }
          let hrow : LowersGuardedTransitionGuardSlack D transition row :=
            readActionSlackRow3Description_lowersGuardedTransitionGuardSlack
              D transition hD read0 read1 read2 write0? move0
              write1? move1 write2? move2 rfl rfl
          refine
            { subroutineReady :=
                canonicalPrimitiveSeqDescription_subroutineReady
                  hrow.subroutineReady hrefresh.subroutineReady
              realizes := ?_ }
          intro c hc hsource hcurrentReads
          rcases hrow.realizes c hc hsource hcurrentReads with
            ⟨physical, hendpoint, hrowHalts⟩
          have hlen : c.tapes.length = 3 := by
            simpa [hD] using hc
          rcases list_eq_three_of_length_eq_three hlen with
            ⟨T, U, V, htapes⟩
          cases c with
          | mk state tapes =>
              simp at htapes
              cases htapes
              have hrefreshHalts :
                  refresh.HaltsFromTapeEquiv physical
                    (encodedGuardedStructuredTapes
                      (D.applyActions
                        [ { write? := write0?, move := move0 }
                        , { write? := write1?, move := move1 }
                        , { write? := write2?, move := move2 } ]
                        [T, U, V])) :=
                hrefresh.realizes_transitionPrimitiveSequenceOfRow3_guardSlackEndpoint
                  transition read0 read1 read2
                  ({ write? := write0?, move := move0 } : TapeAction)
                  ({ write? := write1?, move := move1 } : TapeAction)
                  ({ write? := write2?, move := move2 } : TapeAction)
                  T U V rfl rfl hendpoint
              have hcomposed :=
                canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                  hrow.subroutineReady hrefresh.subroutineReady
                  hrowHalts hrefreshHalts
              simpa [row, transition,
                readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh]
                using hcomposed

theorem readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh_lowersGuardedTransitionEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsReadWriteRow3 t = true)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh_lowersGuardedTransitionEquiv
    D t hD
    (supportedReadWriteRow3_of_supports_eq_true hsupported)
    hrefresh

theorem readActionSlackRow3DescriptionOfRowWithStructuredSingleton3Refresh_lowersGuardedTransitionEquiv
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : SupportedReadWriteRow3 t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) := by
  cases hsupported with
  | mk read0 read1 read2 write0? write1? write2? move0 move1 move2
      hreads hactions =>
      cases t with
      | mk source reads actions target =>
          simp [readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh]
            at hreads hactions ⊢
          cases hreads
          cases hactions
          let row :=
            readActionSlackRow3Description read0 read1 read2
              write0? move0 write1? move1 write2? move2
          let transition : Transition :=
            { source := source
              reads := [read0, read1, read2]
              actions :=
                [ { write? := write0?, move := move0 }
                , { write? := write1?, move := move1 }
                , { write? := write2?, move := move2 } ]
              target := target }
          let hrow : LowersGuardedTransitionGuardSlack D transition row :=
            readActionSlackRow3Description_lowersGuardedTransitionGuardSlack
              D transition hD read0 read1 read2 write0? move0
              write1? move1 write2? move2 rfl rfl
          refine
            { subroutineReady :=
                canonicalPrimitiveSeqDescription_subroutineReady
                  hrow.subroutineReady hrefresh.subroutineReady
              realizes := ?_ }
          intro c hc hsource hcurrentReads
          rcases hrow.realizes c hc hsource hcurrentReads with
            ⟨physical, hendpoint, hrowHalts⟩
          have hlen : c.tapes.length = 3 := by
            simpa [hD] using hc
          rcases list_eq_three_of_length_eq_three hlen with
            ⟨T, U, V, htapes⟩
          cases c with
          | mk state tapes =>
              simp at htapes
              cases htapes
              have hrefreshHalts :
                  refresh.HaltsFromTapeEquiv physical
                    (encodedGuardedStructuredTapes
                      (D.applyActions
                        [ { write? := write0?, move := move0 }
                        , { write? := write1?, move := move1 }
                        , { write? := write2?, move := move2 } ]
                        [T, U, V])) :=
                hrefresh.realizes_transitionPrimitiveSequenceOfRow3_guardSlackEndpoint
                  transition read0 read1 read2
                  ({ write? := write0?, move := move0 } : TapeAction)
                  ({ write? := write1?, move := move1 } : TapeAction)
                  ({ write? := write2?, move := move2 } : TapeAction)
                  T U V rfl rfl hendpoint
              have hcomposed :=
                canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
                  hrow.subroutineReady hrefresh.subroutineReady
                  hrowHalts hrefreshHalts
              simpa [row, transition,
                readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh]
                using hcomposed

theorem readActionSlackRow3DescriptionOfRowWithStructuredSingleton3Refresh_lowersGuardedTransitionEquiv_of_supports
    (D : Description) (t : Transition)
    (hD : D.tapeCount = 3)
    (hsupported : supportsReadWriteRow3 t = true)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  readActionSlackRow3DescriptionOfRowWithStructuredSingleton3Refresh_lowersGuardedTransitionEquiv
    D t hD
    (supportedReadWriteRow3_of_supports_eq_true hsupported)
    hrefresh

structure SupportsReadWriteRows3
    (D : Description) : Prop where
  tapeCount_eq : D.tapeCount = 3
  rows_supported :
    forall t : Transition,
      t ∈ D.transitions ->
        supportsReadWriteRow3 t = true

def supportsReadWriteRows3
    (D : Description) : Bool :=
  if D.tapeCount = 3 then
    D.transitions.all supportsReadWriteRow3
  else
    false

theorem supportsReadWriteRows3_eq_true_of_supported
    {D : Description}
    (hD : SupportsReadWriteRows3 D) :
    supportsReadWriteRows3 D = true := by
  simp [supportsReadWriteRows3, hD.tapeCount_eq]
  exact hD.rows_supported

theorem supportedReadWriteRows3_of_supports_eq_true
    {D : Description}
    (hD : supportsReadWriteRows3 D = true) :
    SupportsReadWriteRows3 D := by
  by_cases htapes : D.tapeCount = 3
  · have hrows :
        D.transitions.all supportsReadWriteRow3 = true := by
      simpa [supportsReadWriteRows3, htapes] using hD
    exact
      { tapeCount_eq := htapes
        rows_supported := by
          intro t ht
          exact List.all_eq_true.mp hrows t ht }
  · simp [supportsReadWriteRows3, htapes] at hD

theorem supportsReadWriteRows3_eq_true_iff
    (D : Description) :
    supportsReadWriteRows3 D = true ↔
      SupportsReadWriteRows3 D :=
  ⟨supportedReadWriteRows3_of_supports_eq_true,
    supportsReadWriteRows3_eq_true_of_supported⟩

theorem SupportsReadWriteRows3.row_lowersGuardedTransitionEquiv_withRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {t : Transition} (ht : t ∈ D.transitions)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteRow3DescriptionOfRowWithRefresh t refresh) :=
  readWriteRow3DescriptionOfRowWithRefresh_lowersGuardedTransitionEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht) hrefresh

theorem SupportsReadWriteRows3.row_lowersGuardedTransitionLogicalEquiv
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {t : Transition} (ht : t ∈ D.transitions) :
    LowersGuardedTransitionLogicalEquiv D t
      (readActionSlackRow3DescriptionOfRow t) :=
  readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionLogicalEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht)

theorem SupportsReadWriteRows3.row_lowersGuardedTransitionGuardSlack
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {t : Transition} (ht : t ∈ D.transitions) :
    LowersGuardedTransitionGuardSlack D t
      (readActionSlackRow3DescriptionOfRow t) :=
  readActionSlackRow3DescriptionOfRow_lowersGuardedTransitionGuardSlack_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht)

theorem SupportsReadWriteRows3.row_lowersGuardedTransitionEquiv_withGuardSlackRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {t : Transition} (ht : t ∈ D.transitions)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh) :=
  readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh_lowersGuardedTransitionEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht) hrefresh

theorem SupportsReadWriteRows3.row_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {t : Transition} (ht : t ∈ D.transitions)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh_lowersGuardedTransitionEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht) hrefresh

theorem SupportsReadWriteRows3.row_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {t : Transition} (ht : t ∈ D.transitions)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  readActionSlackRow3DescriptionOfRowWithStructuredSingleton3Refresh_lowersGuardedTransitionEquiv_of_supports
    D t hD.tapeCount_eq (hD.rows_supported t ht) hrefresh

theorem SupportsReadWriteRows3.lookup_lowersGuardedTransitionEquiv_withRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteRow3DescriptionOfRowWithRefresh t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withRefresh
    (Description.lookupTransition_mem hlookup) hrefresh

theorem SupportsReadWriteRows3.lookup_lowersGuardedTransitionLogicalEquiv
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    LowersGuardedTransitionLogicalEquiv D t
      (readActionSlackRow3DescriptionOfRow t) :=
  hD.row_lowersGuardedTransitionLogicalEquiv
    (Description.lookupTransition_mem hlookup)

theorem SupportsReadWriteRows3.lookup_lowersGuardedTransitionGuardSlack
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    LowersGuardedTransitionGuardSlack D t
      (readActionSlackRow3DescriptionOfRow t) :=
  hD.row_lowersGuardedTransitionGuardSlack
    (Description.lookupTransition_mem hlookup)

theorem SupportsReadWriteRows3.lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withGuardSlackRefresh
    (Description.lookupTransition_mem hlookup) hrefresh

theorem SupportsReadWriteRows3.lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
    (Description.lookupTransition_mem hlookup) hrefresh

theorem SupportsReadWriteRows3.lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  hD.row_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
    (Description.lookupTransition_mem hlookup) hrefresh

theorem lookup_lowersGuardedTransitionLogicalEquiv_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    LowersGuardedTransitionLogicalEquiv D t
      (readActionSlackRow3DescriptionOfRow t) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionLogicalEquiv hlookup

theorem lookup_lowersGuardedTransitionGuardSlack_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t) :
    LowersGuardedTransitionGuardSlack D t
      (readActionSlackRow3DescriptionOfRow t) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionGuardSlack hlookup

theorem lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh
      hlookup hrefresh

theorem lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
      hlookup hrefresh

theorem lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    LowersGuardedTransitionEquiv D t
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
      hlookup hrefresh

theorem SupportsReadWriteRows3.lookup_realizes_structured_step_withRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    D.stepConfig c = some next ∧
      (readWriteRow3DescriptionOfRowWithRefresh
        t refresh).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) :=
  lowersGuardedTransitionEquiv_realizes_structured_step
    (hD.lookup_lowersGuardedTransitionEquiv_withRefresh
      hlookup hrefresh)
    hc hlookup hnext

theorem SupportsReadWriteRows3.lookup_realizes_structured_step_withGuardSlackRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    D.stepConfig c = some next ∧
      (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
        t refresh).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) :=
  lowersGuardedTransitionEquiv_realizes_structured_step
    (hD.lookup_lowersGuardedTransitionEquiv_withGuardSlackRefresh
      hlookup hrefresh)
    hc hlookup hnext

theorem SupportsReadWriteRows3.lookup_realizes_structured_step_withStructuredSingletonRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    D.stepConfig c = some next ∧
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) :=
  lowersGuardedTransitionEquiv_realizes_structured_step
    (hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingletonRefresh
      hlookup hrefresh)
    hc hlookup hnext

theorem SupportsReadWriteRows3.lookup_realizes_structured_step_withStructuredSingleton3Refresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    D.stepConfig c = some next ∧
      (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
        t refresh).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes c.tapes)
        (encodedGuardedStructuredTapes next.tapes) :=
  lowersGuardedTransitionEquiv_realizes_structured_step
    (hD.lookup_lowersGuardedTransitionEquiv_withStructuredSingleton3Refresh
      hlookup hrefresh)
    hc hlookup hnext

theorem SupportsReadWriteRows3.lookup_realizes_structured_step
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration} {t : Transition}
    (hstate : next.state < D.stateCount)
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      exists physical : Tape Bool,
        StructuredLogicalEquivEncodedConfig D next physical ∧
          (readActionSlackRow3DescriptionOfRow t).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            physical :=
  let hstep :=
    lowersGuardedTransitionLogicalEquiv_realizes_structured_step
      (hD.lookup_lowersGuardedTransitionLogicalEquiv hlookup)
      hc hlookup hnext
  ⟨hstep.left, by
    rcases hstep.right with
      ⟨physical, hphysical, hhalts⟩
    exact
      ⟨physical,
        ⟨hstate, Description.stepConfig_tape_count hstep.left, hphysical⟩,
        hhalts⟩⟩

theorem SupportsReadWriteRows3.lookup_realizes_structured_step_of_wellFormed
    {D : Description} (hD : SupportsReadWriteRows3 D)
    (hwellFormed : D.WellFormed)
    {c next : Configuration} {t : Transition}
    (hc : c.tapes.length = D.tapeCount)
    (hlookup : D.lookupTransition c = some t)
    (hnext : next = structuredTransitionTarget D t c) :
    D.stepConfig c = some next ∧
      exists physical : Tape Bool,
        StructuredLogicalEquivEncodedConfig D next physical ∧
          (readActionSlackRow3DescriptionOfRow t).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            physical :=
  let hstep := stepConfig_eq_some_of_lookupTransition hlookup
  hD.lookup_realizes_structured_step
    (Description.stepConfig_state_bound hwellFormed (by
      rw [hnext]
      exact hstep))
    hc hlookup hnext

theorem SupportsReadWriteRows3.stepConfig_realizes_structured_step_withRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readWriteRow3DescriptionOfRowWithRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_withRefresh
          hc hlookup hnext hrefresh
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem SupportsReadWriteRows3.stepConfig_realizes_structured_step_withGuardSlackRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_withGuardSlackRefresh
          hc hlookup hnext hrefresh
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem SupportsReadWriteRows3.stepConfig_realizes_structured_step_withStructuredSingletonRefresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_withStructuredSingletonRefresh
          hc hlookup hnext hrefresh
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem SupportsReadWriteRows3.stepConfig_realizes_structured_step_withStructuredSingleton3Refresh
    {D : Description} (hD : SupportsReadWriteRows3 D)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_withStructuredSingleton3Refresh
          hc hlookup hnext hrefresh
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem SupportsReadWriteRows3.stepConfig_realizes_structured_step
    {D : Description} (hD : SupportsReadWriteRows3 D)
    (hwellFormed : D.WellFormed)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          exists physical : Tape Bool,
            StructuredLogicalEquivEncodedConfig D next physical ∧
              (readActionSlackRow3DescriptionOfRow t).HaltsFromTapeEquiv
                (encodedGuardedStructuredTapes c.tapes)
                physical := by
  cases hlookup : D.lookupTransition c with
  | none =>
      simp [Description.stepConfig, hlookup] at hstep
  | some t =>
      have hstepLookup :
          D.stepConfig c =
            some (structuredTransitionTarget D t c) :=
        stepConfig_eq_some_of_lookupTransition hlookup
      have hnext : next = structuredTransitionTarget D t c := by
        rw [hstep] at hstepLookup
        exact Option.some.inj hstepLookup
      have hreal :=
        hD.lookup_realizes_structured_step_of_wellFormed
          hwellFormed hc hlookup hnext
      exact ⟨t, rfl, hnext, hreal.right⟩

theorem lookup_lowersGuardedTransitionEquiv_withRefresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c : Configuration} {t : Transition}
    (hlookup : D.lookupTransition c = some t)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    LowersGuardedTransitionEquiv D t
      (readWriteRow3DescriptionOfRowWithRefresh t refresh) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.lookup_lowersGuardedTransitionEquiv_withRefresh hlookup hrefresh

theorem stepConfig_realizes_structured_step_withRefresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : LogicalEquivGuardRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readWriteRow3DescriptionOfRowWithRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step_withRefresh
      hc hstep hrefresh

theorem stepConfig_realizes_structured_step_withGuardSlackRefresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : GuardSlackRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readActionSlackRow3DescriptionOfRowWithGuardSlackRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step_withGuardSlackRefresh
      hc hstep hrefresh

theorem stepConfig_realizes_structured_step_withStructuredSingletonRefresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefreshContract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step_withStructuredSingletonRefresh
      hc hstep hrefresh

theorem stepConfig_realizes_structured_step_withStructuredSingleton3Refresh_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next)
    {refresh : MachineDescription}
    (hrefresh : StructuredSingletonGuardSlackRefresh3Contract refresh) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          (readActionSlackRow3DescriptionOfRowWithStructuredSingletonRefresh
            t refresh).HaltsFromTapeEquiv
            (encodedGuardedStructuredTapes c.tapes)
            (encodedGuardedStructuredTapes next.tapes) :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step_withStructuredSingleton3Refresh
      hc hstep hrefresh

theorem stepConfig_realizes_structured_step_of_supportsReadWriteRows3
    {D : Description}
    (hD : supportsReadWriteRows3 D = true)
    (hwellFormed : D.WellFormed)
    {c next : Configuration}
    (hc : c.tapes.length = D.tapeCount)
    (hstep : D.stepConfig c = some next) :
    exists t : Transition,
      D.lookupTransition c = some t ∧
        next = structuredTransitionTarget D t c ∧
          exists physical : Tape Bool,
            StructuredLogicalEquivEncodedConfig D next physical ∧
              (readActionSlackRow3DescriptionOfRow t).HaltsFromTapeEquiv
                (encodedGuardedStructuredTapes c.tapes)
                physical :=
  (supportedReadWriteRows3_of_supports_eq_true hD)
    |>.stepConfig_realizes_structured_step hwellFormed hc hstep

end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround
end Computability
end FoC

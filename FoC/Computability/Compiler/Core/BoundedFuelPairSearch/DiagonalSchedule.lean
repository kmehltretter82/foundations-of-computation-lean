import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SuccessOnlyRecognizer

set_option doc.verso true

/-!
# Bound-free fair schedule

The persistent search loop stores exactly its four semantic coordinates.  A
diagonal successor enumerates all four-tuples without storing a fifth common
bound: mass moves from left to right within one diagonal, then the completed
diagonal becomes the leftmost coordinate of the next one.
-/

namespace FoC
namespace Computability
namespace BoundedFuelPairSearch

/-- Four-coordinate cursor used by the persistent physical search loop. -/
structure SuccessOnlyDiagonalCursor where
  limit : Nat
  candidateFuel : Nat
  sourceFuel : Nat
  checkerFuel : Nat
deriving DecidableEq

/-- Origin of the four-dimensional diagonal enumeration. -/
def SuccessOnlyDiagonalCursor.initial : SuccessOnlyDiagonalCursor :=
  ⟨0, 0, 0, 0⟩

/-- Advance to the next point of the four-dimensional diagonal enumeration. -/
def SuccessOnlyDiagonalCursor.advance
    (cursor : SuccessOnlyDiagonalCursor) : SuccessOnlyDiagonalCursor :=
  if 0 < cursor.limit then
    ⟨cursor.limit - 1, cursor.candidateFuel + 1,
      cursor.sourceFuel, cursor.checkerFuel⟩
  else if 0 < cursor.candidateFuel then
    ⟨cursor.candidateFuel - 1, 0,
      cursor.sourceFuel + 1, cursor.checkerFuel⟩
  else if 0 < cursor.sourceFuel then
    ⟨cursor.sourceFuel - 1, 0, 0, cursor.checkerFuel + 1⟩
  else
    ⟨cursor.checkerFuel + 1, 0, 0, 0⟩

/-- Iterate the bound-free diagonal successor. -/
def SuccessOnlyDiagonalCursor.advanceN :
    Nat -> SuccessOnlyDiagonalCursor -> SuccessOnlyDiagonalCursor
  | 0, cursor => cursor
  | steps + 1, cursor =>
      (SuccessOnlyDiagonalCursor.advanceN steps cursor).advance

/-- Reachability from the unique diagonal origin. -/
def SuccessOnlyDiagonalCursor.Reachable
    (cursor : SuccessOnlyDiagonalCursor) : Prop :=
  exists steps,
    SuccessOnlyDiagonalCursor.advanceN steps
      SuccessOnlyDiagonalCursor.initial = cursor

theorem SuccessOnlyDiagonalCursor.reachable_initial :
    SuccessOnlyDiagonalCursor.initial.Reachable :=
  ⟨0, rfl⟩

theorem SuccessOnlyDiagonalCursor.reachable_advance
    {cursor : SuccessOnlyDiagonalCursor}
    (hcursor : cursor.Reachable) : cursor.advance.Reachable := by
  rcases hcursor with ⟨steps, hsteps⟩
  exact ⟨steps + 1, by
    simp [SuccessOnlyDiagonalCursor.advanceN, hsteps]⟩

theorem SuccessOnlyDiagonalCursor.reachable_candidateFuel
    (limit candidateFuel sourceFuel checkerFuel : Nat)
    (hbase :
      SuccessOnlyDiagonalCursor.Reachable
        ⟨limit + candidateFuel, 0, sourceFuel, checkerFuel⟩) :
    SuccessOnlyDiagonalCursor.Reachable
      ⟨limit, candidateFuel, sourceFuel, checkerFuel⟩ := by
  induction candidateFuel generalizing limit with
  | zero => simpa using hbase
  | succ candidateFuel ih =>
      have hprevious := ih (limit + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbase)
      have hnext :=
        SuccessOnlyDiagonalCursor.reachable_advance hprevious
      simpa [SuccessOnlyDiagonalCursor.advance] using hnext

theorem SuccessOnlyDiagonalCursor.reachable_sourceFuel
    (limit candidateFuel sourceFuel checkerFuel : Nat)
    (hbase :
      SuccessOnlyDiagonalCursor.Reachable
        ⟨limit + candidateFuel + sourceFuel, 0, 0, checkerFuel⟩) :
    SuccessOnlyDiagonalCursor.Reachable
      ⟨limit, candidateFuel, sourceFuel, checkerFuel⟩ := by
  induction sourceFuel generalizing limit candidateFuel with
  | zero =>
      exact SuccessOnlyDiagonalCursor.reachable_candidateFuel
        limit candidateFuel 0 checkerFuel (by simpa using hbase)
  | succ sourceFuel ih =>
      have hprevious := ih 0 (limit + candidateFuel + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbase)
      have hnext :=
        SuccessOnlyDiagonalCursor.reachable_advance hprevious
      have hstart :
          SuccessOnlyDiagonalCursor.Reachable
            ⟨limit + candidateFuel, 0, sourceFuel + 1, checkerFuel⟩ := by
        simpa [SuccessOnlyDiagonalCursor.advance] using hnext
      exact SuccessOnlyDiagonalCursor.reachable_candidateFuel
        limit candidateFuel (sourceFuel + 1) checkerFuel hstart

theorem SuccessOnlyDiagonalCursor.reachable_checkerFuel
    (limit candidateFuel sourceFuel checkerFuel : Nat)
    (hbase :
      SuccessOnlyDiagonalCursor.Reachable
        ⟨limit + candidateFuel + sourceFuel + checkerFuel, 0, 0, 0⟩) :
    SuccessOnlyDiagonalCursor.Reachable
      ⟨limit, candidateFuel, sourceFuel, checkerFuel⟩ := by
  induction checkerFuel generalizing limit candidateFuel sourceFuel with
  | zero =>
      exact SuccessOnlyDiagonalCursor.reachable_sourceFuel
        limit candidateFuel sourceFuel 0 (by simpa using hbase)
  | succ checkerFuel ih =>
      have hprevious :=
        ih 0 0 (limit + candidateFuel + sourceFuel + 1) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbase)
      have hnext :=
        SuccessOnlyDiagonalCursor.reachable_advance hprevious
      have hstart :
          SuccessOnlyDiagonalCursor.Reachable
            ⟨limit + candidateFuel + sourceFuel,
              0, 0, checkerFuel + 1⟩ := by
        simpa [SuccessOnlyDiagonalCursor.advance] using hnext
      exact SuccessOnlyDiagonalCursor.reachable_sourceFuel
        limit candidateFuel sourceFuel (checkerFuel + 1) hstart

theorem SuccessOnlyDiagonalCursor.reachable_diagonal_start
    (total : Nat) :
    SuccessOnlyDiagonalCursor.Reachable ⟨total, 0, 0, 0⟩ := by
  induction total with
  | zero =>
      simpa [SuccessOnlyDiagonalCursor.initial] using
        SuccessOnlyDiagonalCursor.reachable_initial
  | succ total ih =>
      have hend :=
        SuccessOnlyDiagonalCursor.reachable_checkerFuel
          0 0 0 total (by simpa using ih)
      have hnext :=
        SuccessOnlyDiagonalCursor.reachable_advance hend
      simpa [SuccessOnlyDiagonalCursor.advance] using hnext

/-- Every four-coordinate cursor occurs in the diagonal schedule. -/
theorem successOnlyDiagonalCursor_reachable
    (cursor : SuccessOnlyDiagonalCursor) : cursor.Reachable := by
  rcases cursor with ⟨limit, candidateFuel, sourceFuel, checkerFuel⟩
  exact SuccessOnlyDiagonalCursor.reachable_checkerFuel
    limit candidateFuel sourceFuel checkerFuel
    (SuccessOnlyDiagonalCursor.reachable_diagonal_start
      (limit + candidateFuel + sourceFuel + checkerFuel))

/-- Every bounded semantic search index occurs without storing its bound. -/
theorem successOnlyScheduleIndex_reachable_diagonal
    (index : SuccessOnlyScheduleIndex) :
    SuccessOnlyDiagonalCursor.Reachable
      ⟨index.limit, index.candidateFuel,
        index.sourceFuel, index.checkerFuel⟩ :=
  successOnlyDiagonalCursor_reachable _

end BoundedFuelPairSearch
end Computability
end FoC

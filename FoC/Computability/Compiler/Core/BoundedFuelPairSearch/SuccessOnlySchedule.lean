import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SuccessOnlyRecognizer

set_option doc.verso true

/-!
# Success-only fair schedule

Pure lexicographic enumeration of the four bounded coordinates used by the
success-only fuel-pair search.  The checker fuel varies fastest; completing a
finite four-dimensional cube advances to the next common bound.
-/

namespace FoC
namespace Computability
namespace BoundedFuelPairSearch

/-- Cursor for a finite four-dimensional search cube. -/
structure SuccessOnlyScheduleCursor where
  bound : Nat
  limit : Nat
  candidateFuel : Nat
  sourceFuel : Nat
  checkerFuel : Nat
deriving DecidableEq

/-- Every coordinate of a valid cursor lies in its current search cube. -/
def SuccessOnlyScheduleCursor.Valid
    (cursor : SuccessOnlyScheduleCursor) : Prop :=
  cursor.limit ≤ cursor.bound ∧
    cursor.candidateFuel ≤ cursor.bound ∧
      cursor.sourceFuel ≤ cursor.bound ∧
        cursor.checkerFuel ≤ cursor.bound

/-- Unique origin of the fair schedule. -/
def SuccessOnlyScheduleCursor.initial : SuccessOnlyScheduleCursor :=
  ⟨0, 0, 0, 0, 0⟩

@[simp] theorem SuccessOnlyScheduleCursor.initial_valid :
    SuccessOnlyScheduleCursor.initial.Valid := by
  simp [SuccessOnlyScheduleCursor.initial, SuccessOnlyScheduleCursor.Valid]

/-- Advance in lexicographic order, with checker fuel varying fastest. -/
def SuccessOnlyScheduleCursor.advance
    (cursor : SuccessOnlyScheduleCursor) : SuccessOnlyScheduleCursor :=
  if cursor.checkerFuel < cursor.bound then
    ⟨cursor.bound, cursor.limit, cursor.candidateFuel,
      cursor.sourceFuel, cursor.checkerFuel + 1⟩
  else if cursor.sourceFuel < cursor.bound then
    ⟨cursor.bound, cursor.limit, cursor.candidateFuel,
      cursor.sourceFuel + 1, 0⟩
  else if cursor.candidateFuel < cursor.bound then
    ⟨cursor.bound, cursor.limit, cursor.candidateFuel + 1, 0, 0⟩
  else if cursor.limit < cursor.bound then
    ⟨cursor.bound, cursor.limit + 1, 0, 0, 0⟩
  else
    ⟨cursor.bound + 1, 0, 0, 0, 0⟩

theorem SuccessOnlyScheduleCursor.advance_valid
    (cursor : SuccessOnlyScheduleCursor)
    (hvalid : cursor.Valid) : cursor.advance.Valid := by
  rcases cursor with
    ⟨bound, limit, candidateFuel, sourceFuel, checkerFuel⟩
  rcases hvalid with ⟨hlimit, hcandidateFuel, hsourceFuel, hcheckerFuel⟩
  simp only at hlimit hcandidateFuel hsourceFuel hcheckerFuel
  simp only [SuccessOnlyScheduleCursor.advance]
  split
  · exact ⟨hlimit, hcandidateFuel, hsourceFuel, by lia⟩
  · split
    · exact ⟨hlimit, hcandidateFuel, by lia, Nat.zero_le bound⟩
    · split
      · exact ⟨hlimit, by lia, Nat.zero_le bound, Nat.zero_le bound⟩
      · split
        · exact ⟨by lia, Nat.zero_le bound,
            Nat.zero_le bound, Nat.zero_le bound⟩
        · exact ⟨Nat.zero_le (bound + 1), Nat.zero_le (bound + 1),
            Nat.zero_le (bound + 1), Nat.zero_le (bound + 1)⟩

/-- Iterate the pure schedule transition for the requested number of steps. -/
def SuccessOnlyScheduleCursor.advanceN :
    Nat -> SuccessOnlyScheduleCursor -> SuccessOnlyScheduleCursor
  | 0, cursor => cursor
  | steps + 1, cursor =>
      (SuccessOnlyScheduleCursor.advanceN steps cursor).advance

/-- Reachability from the unique fair-schedule origin. -/
def SuccessOnlyScheduleCursor.Reachable
    (cursor : SuccessOnlyScheduleCursor) : Prop :=
  exists steps : Nat,
    SuccessOnlyScheduleCursor.advanceN steps
      SuccessOnlyScheduleCursor.initial = cursor

theorem SuccessOnlyScheduleCursor.reachable_initial :
    SuccessOnlyScheduleCursor.initial.Reachable := by
  exact ⟨0, rfl⟩

theorem SuccessOnlyScheduleCursor.reachable_advance
    {cursor : SuccessOnlyScheduleCursor}
    (hcursor : cursor.Reachable) : cursor.advance.Reachable := by
  rcases hcursor with ⟨steps, hsteps⟩
  refine ⟨steps + 1, ?_⟩
  simp [SuccessOnlyScheduleCursor.advanceN, hsteps]

theorem SuccessOnlyScheduleCursor.reachable_checkerFuel
    (bound limit candidateFuel sourceFuel checkerFuel : Nat)
    (hbase :
      SuccessOnlyScheduleCursor.Reachable
        ⟨bound, limit, candidateFuel, sourceFuel, 0⟩)
    (hcheckerFuel : checkerFuel ≤ bound) :
    SuccessOnlyScheduleCursor.Reachable
      ⟨bound, limit, candidateFuel, sourceFuel, checkerFuel⟩ := by
  induction checkerFuel with
  | zero => exact hbase
  | succ checkerFuel ih =>
      have hprevious := ih (by lia)
      have hnext := SuccessOnlyScheduleCursor.reachable_advance hprevious
      simpa [SuccessOnlyScheduleCursor.advance,
        show checkerFuel < bound by lia] using hnext

theorem SuccessOnlyScheduleCursor.reachable_sourceFuel
    (bound limit candidateFuel sourceFuel : Nat)
    (hbase :
      SuccessOnlyScheduleCursor.Reachable
        ⟨bound, limit, candidateFuel, 0, 0⟩)
    (hsourceFuel : sourceFuel ≤ bound) :
    SuccessOnlyScheduleCursor.Reachable
      ⟨bound, limit, candidateFuel, sourceFuel, 0⟩ := by
  induction sourceFuel with
  | zero => exact hbase
  | succ sourceFuel ih =>
      have hrow := ih (by lia)
      have hend := SuccessOnlyScheduleCursor.reachable_checkerFuel
        bound limit candidateFuel sourceFuel bound hrow (Nat.le_refl bound)
      have hnext := SuccessOnlyScheduleCursor.reachable_advance hend
      simpa [SuccessOnlyScheduleCursor.advance,
        show ¬ bound < bound by lia,
        show sourceFuel < bound by lia] using hnext

theorem SuccessOnlyScheduleCursor.reachable_candidateFuel
    (bound limit candidateFuel : Nat)
    (hbase :
      SuccessOnlyScheduleCursor.Reachable
        ⟨bound, limit, 0, 0, 0⟩)
    (hcandidateFuel : candidateFuel ≤ bound) :
    SuccessOnlyScheduleCursor.Reachable
      ⟨bound, limit, candidateFuel, 0, 0⟩ := by
  induction candidateFuel with
  | zero => exact hbase
  | succ candidateFuel ih =>
      have hcandidate := ih (by lia)
      have hsourceEnd := SuccessOnlyScheduleCursor.reachable_sourceFuel
        bound limit candidateFuel bound hcandidate (Nat.le_refl bound)
      have hcheckerEnd := SuccessOnlyScheduleCursor.reachable_checkerFuel
        bound limit candidateFuel bound bound hsourceEnd (Nat.le_refl bound)
      have hnext := SuccessOnlyScheduleCursor.reachable_advance hcheckerEnd
      simpa [SuccessOnlyScheduleCursor.advance,
        show ¬ bound < bound by lia,
        show candidateFuel < bound by lia] using hnext

theorem SuccessOnlyScheduleCursor.reachable_limit
    (bound limit : Nat)
    (hbase :
      SuccessOnlyScheduleCursor.Reachable
        ⟨bound, 0, 0, 0, 0⟩)
    (hlimit : limit ≤ bound) :
    SuccessOnlyScheduleCursor.Reachable
      ⟨bound, limit, 0, 0, 0⟩ := by
  induction limit with
  | zero => exact hbase
  | succ limit ih =>
      have hlimitStart := ih (by lia)
      have hcandidateEnd :=
        SuccessOnlyScheduleCursor.reachable_candidateFuel
          bound limit bound hlimitStart (Nat.le_refl bound)
      have hsourceEnd := SuccessOnlyScheduleCursor.reachable_sourceFuel
        bound limit bound bound hcandidateEnd (Nat.le_refl bound)
      have hcheckerEnd := SuccessOnlyScheduleCursor.reachable_checkerFuel
        bound limit bound bound bound hsourceEnd (Nat.le_refl bound)
      have hnext := SuccessOnlyScheduleCursor.reachable_advance hcheckerEnd
      simpa [SuccessOnlyScheduleCursor.advance,
        show ¬ bound < bound by lia,
        show limit < bound by lia] using hnext

theorem SuccessOnlyScheduleCursor.reachable_square_start (bound : Nat) :
    SuccessOnlyScheduleCursor.Reachable ⟨bound, 0, 0, 0, 0⟩ := by
  induction bound with
  | zero =>
      simpa [SuccessOnlyScheduleCursor.initial] using
        SuccessOnlyScheduleCursor.reachable_initial
  | succ bound ih =>
      have hlimitEnd := SuccessOnlyScheduleCursor.reachable_limit
        bound bound ih (Nat.le_refl bound)
      have hcandidateEnd :=
        SuccessOnlyScheduleCursor.reachable_candidateFuel
          bound bound bound hlimitEnd (Nat.le_refl bound)
      have hsourceEnd := SuccessOnlyScheduleCursor.reachable_sourceFuel
        bound bound bound bound hcandidateEnd (Nat.le_refl bound)
      have hcheckerEnd := SuccessOnlyScheduleCursor.reachable_checkerFuel
        bound bound bound bound bound hsourceEnd (Nat.le_refl bound)
      have hnext := SuccessOnlyScheduleCursor.reachable_advance hcheckerEnd
      simpa [SuccessOnlyScheduleCursor.advance,
        show ¬ bound < bound by lia] using hnext

/-- Every point of every finite search cube occurs in the fair schedule. -/
theorem successOnlyScheduleCursor_reachable_of_valid
    (cursor : SuccessOnlyScheduleCursor)
    (hvalid : cursor.Valid) : cursor.Reachable := by
  rcases cursor with
    ⟨bound, limit, candidateFuel, sourceFuel, checkerFuel⟩
  rcases hvalid with ⟨hlimit, hcandidateFuel, hsourceFuel, hcheckerFuel⟩
  have hsquare := SuccessOnlyScheduleCursor.reachable_square_start bound
  have hlimitReach := SuccessOnlyScheduleCursor.reachable_limit
    bound limit hsquare (by simpa using hlimit)
  have hcandidateReach := SuccessOnlyScheduleCursor.reachable_candidateFuel
    bound limit candidateFuel hlimitReach (by simpa using hcandidateFuel)
  have hsourceReach := SuccessOnlyScheduleCursor.reachable_sourceFuel
    bound limit candidateFuel sourceFuel hcandidateReach
      (by simpa using hsourceFuel)
  exact SuccessOnlyScheduleCursor.reachable_checkerFuel
    bound limit candidateFuel sourceFuel checkerFuel hsourceReach
      (by simpa using hcheckerFuel)

/-- Every semantic success-only search index occurs in the concrete schedule. -/
theorem successOnlyScheduleIndex_reachable
    (index : SuccessOnlyScheduleIndex) :
    SuccessOnlyScheduleCursor.Reachable
      ⟨index.scheduleBound, index.limit, index.candidateFuel,
        index.sourceFuel, index.checkerFuel⟩ := by
  exact successOnlyScheduleCursor_reachable_of_valid _
    ⟨index.limit_le, index.candidateFuel_le,
      index.sourceFuel_le, index.checkerFuel_le⟩

end BoundedFuelPairSearch
end Computability
end FoC

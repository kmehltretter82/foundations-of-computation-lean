import FoC.Computability.Compiler.FST.CountWindow.RawBoundary

set_option doc.verso true

/-!
# Raw-boundary source-branch route contracts

This module exposes the existing all-branch parameterized right-edge route for
nonempty raw layouts.  It is a construction-family boundary, not the final
fixed public core.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def RawBoundarySourceBranchRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool)) : Prop :=
  exists routeDescription : MachineDescription,
    routeDescription.SubroutineReady ∧
      routeDescription.HaltsFromTapeEquiv
        (sourceTape skipped count (some tailFirst :: tail))
        (rightEdgeTape skipped count tailFirst tail)

theorem sourceBranchRouteCountBound_of_nonempty_count_enough
    (skipped count : Word Bool)
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    sourceBranchRouteCountBound skipped count := by
  cases hlayout : List.append skipped count with
  | nil =>
      exact False.elim (hnonempty hlayout)
  | cons bit rest =>
      cases rest with
      | nil =>
          left
          simpa using congrArg List.length hlayout
      | cons next rest =>
          cases rest with
          | nil =>
              right
              left
              have hlength :
                  (List.append skipped count).length = 2 := by
                simpa using congrArg List.length hlayout
              constructor
              · exact hlength
              · have htwo :
                    2 <= (List.append skipped count).length := by
                  rw [hlength]
                  decide
                have hcount := hcountEnough htwo
                rw [hlength] at hcount
                simpa using hcount
          | cons third rest =>
              right
              right
              have hge :
                  3 <= (List.append skipped count).length := by
                rw [hlayout]
                simp
              constructor
              · exact hge
              · have htwo :
                    2 <= (List.append skipped count).length :=
                  Nat.le_trans (by decide) hge
                have hcount := hcountEnough htwo
                have heq :
                    3 * ((List.append skipped count).length - 3) + 6 =
                      3 * ((List.append skipped count).length - 2) + 3 := by
                  lia
                rw [heq]
                exact hcount

theorem rawBoundarySourceBranchRoute
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    RawBoundarySourceBranchRoute
      skipped count tailFirst tail :=
  sourceBranchRouteDescription_exists_haltsFrom_sourceTape_equiv
    skipped count tailFirst tail hbound

theorem rawBoundary_sourceBranchRoute_halts_exists
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hbound : sourceBranchRouteCountBound skipped count) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) :=
  sourceBranchRouteDescription_exists_haltsFrom_sourceTape_equiv
    skipped count tailFirst tail hbound

theorem rawBoundary_sourceBranchRoute_halts_exists_of_nonempty_count_enough
    (skipped count : Word Bool)
    (tailFirst : Bool)
    (tail : List (Option Bool))
    (hnonempty : List.append skipped count ≠ [])
    (hcountEnough :
      2 <= (List.append skipped count).length ->
        3 * ((List.append skipped count).length - 2) + 3 <=
          count.length) :
    exists routeDescription : MachineDescription,
      routeDescription.SubroutineReady ∧
        routeDescription.HaltsFromTapeEquiv
          (sourceTape skipped count (some tailFirst :: tail))
          (rightEdgeTape skipped count tailFirst tail) :=
  rawBoundary_sourceBranchRoute_halts_exists
    skipped count tailFirst tail
    (sourceBranchRouteCountBound_of_nonempty_count_enough
      skipped count hnonempty hcountEnough)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC

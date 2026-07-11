import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.Core.TransitionTableChecks

set_option doc.verso true

/-!
# Parsed-inner transport machines

Finite machines for the parsed-inner post-prefix field transport.  The
transport rebuilds the decoded merge field order to the left of the cell-0
blank sentinel, growing leftward, after a deletion pre-pass has erased the
unselected fields.  This module contains only the machine descriptions, their
readiness trios, and reusable run primitives for crossing bit runs and blank
runs; the per-machine run lemmas live in the sibling modules.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace ParsedInnerTransport

def sFCell : Option Bool := some false
def sTCell : Option Bool := some true

/--
Rewind from the trailing blank region to the leading blank sentinel, then
skip the four transition-token bits; halts on the first bit of the boolWord
input field.
-/
def transportEntryDescription : MachineDescription where
  stateCount := 7
  start := 0
  halt := 6
  transitions :=
    [ transition 0 none none Direction.left 0
    , transition 0 sFCell sFCell Direction.left 1
    , transition 0 sTCell sTCell Direction.left 1
    , transition 1 sFCell sFCell Direction.left 1
    , transition 1 sTCell sTCell Direction.left 1
    , transition 1 none none Direction.right 2
    , transition 2 sFCell sFCell Direction.right 3
    , transition 3 sFCell sFCell Direction.right 4
    , transition 4 sFCell sFCell Direction.right 5
    , transition 5 sTCell sTCell Direction.right 6 ]

/--
Starting on the last cell of a 4-bit token {lit}`[0,c2,c3,c4]`, rewrite it in
place to {lit}`[c2,c3,c4,blank]` and halt on the cell after the token.  Valid
tokens are the done token {lit}`0011` and the cell tokens {lit}`0100`,
{lit}`0101`, {lit}`0110`.
The blanked fourth cell later serves as the stop boundary for the
left-boundary eraser.
-/
def sentinelStashDescription : MachineDescription where
  stateCount := 19
  start := 0
  halt := 18
  transitions :=
    [ transition 0 sFCell sFCell Direction.left 1
    , transition 0 sTCell sTCell Direction.left 2
    , transition 1 sFCell sFCell Direction.left 3
    , transition 1 sTCell sTCell Direction.left 4
    , transition 2 sFCell sFCell Direction.left 5
    , transition 2 sTCell sTCell Direction.left 6
    , transition 3 sTCell sTCell Direction.left 7
    , transition 4 sTCell sTCell Direction.left 8
    , transition 5 sTCell sTCell Direction.left 9
    , transition 6 sFCell sFCell Direction.left 10
    , transition 7 sFCell sTCell Direction.right 11
    , transition 8 sFCell sTCell Direction.right 12
    , transition 9 sFCell sTCell Direction.right 13
    , transition 10 sFCell sFCell Direction.right 14
    , transition 11 sTCell sFCell Direction.right 15
    , transition 12 sTCell sTCell Direction.right 15
    , transition 13 sTCell sFCell Direction.right 16
    , transition 14 sFCell sTCell Direction.right 16
    , transition 15 sFCell sFCell Direction.right 17
    , transition 15 sTCell sFCell Direction.right 17
    , transition 16 sFCell sTCell Direction.right 17
    , transition 16 sTCell sTCell Direction.right 17
    , transition 17 sFCell none Direction.right 18
    , transition 17 sTCell none Direction.right 18 ]

/--
Starting on the first erased cell right of a stashed token
{lit}`[c2,c3,c4,blank]`, restore the token to {lit}`[0,c2,c3,c4]` and halt back
on the starting cell.
-/
def sentinelRestoreDescription : MachineDescription where
  stateCount := 20
  start := 0
  halt := 19
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 sFCell sFCell Direction.left 3
    , transition 2 sTCell sTCell Direction.left 4
    , transition 3 sFCell sFCell Direction.left 5
    , transition 3 sTCell sTCell Direction.left 6
    , transition 4 sFCell sFCell Direction.left 7
    , transition 4 sTCell sTCell Direction.left 8
    , transition 5 sTCell sFCell Direction.right 9
    , transition 6 sTCell sFCell Direction.right 10
    , transition 7 sTCell sFCell Direction.right 11
    , transition 8 sFCell sFCell Direction.right 12
    , transition 9 sFCell sTCell Direction.right 13
    , transition 10 sTCell sTCell Direction.right 14
    , transition 11 sFCell sTCell Direction.right 15
    , transition 12 sTCell sFCell Direction.right 16
    , transition 13 sFCell sFCell Direction.right 17
    , transition 14 sFCell sTCell Direction.right 17
    , transition 15 sTCell sFCell Direction.right 18
    , transition 16 sTCell sTCell Direction.right 18
    , transition 17 none sFCell Direction.right 19
    , transition 18 none sTCell Direction.right 19 ]

/-- Walk right over a blank run; halt on the first bit. -/
def blankRightWalkerDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 sFCell sFCell Direction.left 1
    , transition 0 sTCell sTCell Direction.left 1
    , transition 1 none none Direction.right 2 ]

/--
Accept-branch mid eraser: erase four cells (the accept hit field), keep four
cells (the reject hit field), erase a unary nat field (the outer stage), and
halt on the following cell.
-/
def acceptMidEraserDescription : MachineDescription where
  stateCount := 13
  start := 0
  halt := 12
  transitions :=
    [ transition 0 sFCell none Direction.right 1
    , transition 0 sTCell none Direction.right 1
    , transition 1 sFCell none Direction.right 2
    , transition 1 sTCell none Direction.right 2
    , transition 2 sFCell none Direction.right 3
    , transition 2 sTCell none Direction.right 3
    , transition 3 sFCell none Direction.right 4
    , transition 3 sTCell none Direction.right 4
    , transition 4 sFCell sFCell Direction.right 5
    , transition 4 sTCell sTCell Direction.right 5
    , transition 5 sFCell sFCell Direction.right 6
    , transition 5 sTCell sTCell Direction.right 6
    , transition 6 sFCell sFCell Direction.right 7
    , transition 6 sTCell sTCell Direction.right 7
    , transition 7 sFCell sFCell Direction.right 8
    , transition 7 sTCell sTCell Direction.right 8
    , transition 8 sFCell none Direction.right 9
    , transition 9 sFCell none Direction.right 10
    , transition 10 sTCell none Direction.right 11
    , transition 11 sFCell none Direction.right 8
    , transition 11 sTCell none Direction.right 12 ]

/--
Reject-branch mid eraser: walk right over the erased reject-config region,
keep four cells (the accept hit field), erase four cells (the reject hit
field), erase a unary nat field (the outer stage), and halt on the following
cell.
-/
def rejectMidEraserDescription : MachineDescription where
  stateCount := 13
  start := 0
  halt := 12
  transitions :=
    [ transition 0 none none Direction.right 0
    , transition 0 sFCell sFCell Direction.right 1
    , transition 0 sTCell sTCell Direction.right 1
    , transition 1 sFCell sFCell Direction.right 2
    , transition 1 sTCell sTCell Direction.right 2
    , transition 2 sFCell sFCell Direction.right 3
    , transition 2 sTCell sTCell Direction.right 3
    , transition 3 sFCell sFCell Direction.right 4
    , transition 3 sTCell sTCell Direction.right 4
    , transition 4 sFCell none Direction.right 5
    , transition 4 sTCell none Direction.right 5
    , transition 5 sFCell none Direction.right 6
    , transition 5 sTCell none Direction.right 6
    , transition 6 sFCell none Direction.right 7
    , transition 6 sTCell none Direction.right 7
    , transition 7 sFCell none Direction.right 8
    , transition 7 sTCell none Direction.right 8
    , transition 8 sFCell none Direction.right 9
    , transition 9 sFCell none Direction.right 10
    , transition 10 sTCell none Direction.right 11
    , transition 11 sFCell none Direction.right 8
    , transition 11 sTCell none Direction.right 12 ]

/--
Accept phase 1: from the cell right of the rightmost source run, walk left
over that run and the blank gap, pull the last bit of the next run, carry it
left across gap, run, gap, run, and the cell-0 sentinel, write it on the
first blank past the (empty) block, and halt on the written cell.
-/
def pullFirstAcceptDescription : MachineDescription where
  stateCount := 16
  start := 0
  halt := 15
  transitions :=
    [ transition 0 sFCell sFCell Direction.left 0
    , transition 0 sTCell sTCell Direction.left 0
    , transition 0 none none Direction.left 1
    , transition 1 none none Direction.left 1
    , transition 1 sFCell none Direction.left 2
    , transition 1 sTCell none Direction.left 3
    , transition 2 sFCell sFCell Direction.left 2
    , transition 2 sTCell sTCell Direction.left 2
    , transition 2 none none Direction.left 4
    , transition 3 sFCell sFCell Direction.left 3
    , transition 3 sTCell sTCell Direction.left 3
    , transition 3 none none Direction.left 5
    , transition 4 none none Direction.left 4
    , transition 4 sFCell sFCell Direction.left 6
    , transition 4 sTCell sTCell Direction.left 6
    , transition 5 none none Direction.left 5
    , transition 5 sFCell sFCell Direction.left 7
    , transition 5 sTCell sTCell Direction.left 7
    , transition 6 sFCell sFCell Direction.left 6
    , transition 6 sTCell sTCell Direction.left 6
    , transition 6 none none Direction.left 8
    , transition 7 sFCell sFCell Direction.left 7
    , transition 7 sTCell sTCell Direction.left 7
    , transition 7 none none Direction.left 9
    , transition 8 none none Direction.left 8
    , transition 8 sFCell sFCell Direction.left 10
    , transition 8 sTCell sTCell Direction.left 10
    , transition 9 none none Direction.left 9
    , transition 9 sFCell sFCell Direction.left 11
    , transition 9 sTCell sTCell Direction.left 11
    , transition 10 sFCell sFCell Direction.left 10
    , transition 10 sTCell sTCell Direction.left 10
    , transition 10 none none Direction.left 12
    , transition 11 sFCell sFCell Direction.left 11
    , transition 11 sTCell sTCell Direction.left 11
    , transition 11 none none Direction.left 13
    , transition 12 sFCell sFCell Direction.left 12
    , transition 12 sTCell sTCell Direction.left 12
    , transition 12 none sFCell Direction.left 14
    , transition 13 sFCell sFCell Direction.left 13
    , transition 13 sTCell sTCell Direction.left 13
    , transition 13 none sTCell Direction.left 14
    , transition 14 none none Direction.right 15 ]

/--
Reject phase 1 first pull: starting on the last bit of the rightmost run,
erase it and carry it left across gap, run, gap, run, and the cell-0
sentinel to the (empty) block.
-/
def pullFirstRejectDescription : MachineDescription where
  stateCount := 15
  start := 0
  halt := 14
  transitions :=
    [ transition 0 sFCell none Direction.left 1
    , transition 0 sTCell none Direction.left 2
    , transition 1 sFCell sFCell Direction.left 1
    , transition 1 sTCell sTCell Direction.left 1
    , transition 1 none none Direction.left 3
    , transition 2 sFCell sFCell Direction.left 2
    , transition 2 sTCell sTCell Direction.left 2
    , transition 2 none none Direction.left 4
    , transition 3 none none Direction.left 3
    , transition 3 sFCell sFCell Direction.left 5
    , transition 3 sTCell sTCell Direction.left 5
    , transition 4 none none Direction.left 4
    , transition 4 sFCell sFCell Direction.left 6
    , transition 4 sTCell sTCell Direction.left 6
    , transition 5 sFCell sFCell Direction.left 5
    , transition 5 sTCell sTCell Direction.left 5
    , transition 5 none none Direction.left 7
    , transition 6 sFCell sFCell Direction.left 6
    , transition 6 sTCell sTCell Direction.left 6
    , transition 6 none none Direction.left 8
    , transition 7 none none Direction.left 7
    , transition 7 sFCell sFCell Direction.left 9
    , transition 7 sTCell sTCell Direction.left 9
    , transition 8 none none Direction.left 8
    , transition 8 sFCell sFCell Direction.left 10
    , transition 8 sTCell sTCell Direction.left 10
    , transition 9 sFCell sFCell Direction.left 9
    , transition 9 sTCell sTCell Direction.left 9
    , transition 9 none none Direction.left 11
    , transition 10 sFCell sFCell Direction.left 10
    , transition 10 sTCell sTCell Direction.left 10
    , transition 10 none none Direction.left 12
    , transition 11 sFCell sFCell Direction.left 11
    , transition 11 sTCell sTCell Direction.left 11
    , transition 11 none sFCell Direction.left 13
    , transition 12 sFCell sFCell Direction.left 12
    , transition 12 sTCell sTCell Direction.left 12
    , transition 12 none sTCell Direction.left 13
    , transition 13 none none Direction.right 14 ]

/--
Pull one bit across two interior runs: from the block's leftmost bit, travel
right across block, sentinel blank, run, gap, run, gap, and the pulled field
run; erase the field's rightmost bit; carry it back and prepend it at the
block's left edge.
-/
def pullOneBitJ2Description : MachineDescription where
  stateCount := 21
  start := 0
  halt := 20
  transitions :=
    [ transition 0 sFCell sFCell Direction.right 0
    , transition 0 sTCell sTCell Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 sFCell sFCell Direction.right 1
    , transition 1 sTCell sTCell Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 2
    , transition 2 sFCell sFCell Direction.right 3
    , transition 2 sTCell sTCell Direction.right 3
    , transition 3 sFCell sFCell Direction.right 3
    , transition 3 sTCell sTCell Direction.right 3
    , transition 3 none none Direction.right 4
    , transition 4 none none Direction.right 4
    , transition 4 sFCell sFCell Direction.right 5
    , transition 4 sTCell sTCell Direction.right 5
    , transition 5 sFCell sFCell Direction.right 5
    , transition 5 sTCell sTCell Direction.right 5
    , transition 5 none none Direction.left 6
    , transition 6 sFCell none Direction.left 7
    , transition 6 sTCell none Direction.left 8
    , transition 7 sFCell sFCell Direction.left 7
    , transition 7 sTCell sTCell Direction.left 7
    , transition 7 none none Direction.left 9
    , transition 8 sFCell sFCell Direction.left 8
    , transition 8 sTCell sTCell Direction.left 8
    , transition 8 none none Direction.left 10
    , transition 9 none none Direction.left 9
    , transition 9 sFCell sFCell Direction.left 11
    , transition 9 sTCell sTCell Direction.left 11
    , transition 10 none none Direction.left 10
    , transition 10 sFCell sFCell Direction.left 12
    , transition 10 sTCell sTCell Direction.left 12
    , transition 11 sFCell sFCell Direction.left 11
    , transition 11 sTCell sTCell Direction.left 11
    , transition 11 none none Direction.left 13
    , transition 12 sFCell sFCell Direction.left 12
    , transition 12 sTCell sTCell Direction.left 12
    , transition 12 none none Direction.left 14
    , transition 13 none none Direction.left 13
    , transition 13 sFCell sFCell Direction.left 15
    , transition 13 sTCell sTCell Direction.left 15
    , transition 14 none none Direction.left 14
    , transition 14 sFCell sFCell Direction.left 16
    , transition 14 sTCell sTCell Direction.left 16
    , transition 15 sFCell sFCell Direction.left 15
    , transition 15 sTCell sTCell Direction.left 15
    , transition 15 none none Direction.left 17
    , transition 16 sFCell sFCell Direction.left 16
    , transition 16 sTCell sTCell Direction.left 16
    , transition 16 none none Direction.left 18
    , transition 17 sFCell sFCell Direction.left 17
    , transition 17 sTCell sTCell Direction.left 17
    , transition 17 none sFCell Direction.left 19
    , transition 18 sFCell sFCell Direction.left 18
    , transition 18 sTCell sTCell Direction.left 18
    , transition 18 none sTCell Direction.left 19
    , transition 19 none none Direction.right 20 ]

/-- Pull one bit across one interior run. -/
def pullOneBitJ1Description : MachineDescription where
  stateCount := 15
  start := 0
  halt := 14
  transitions :=
    [ transition 0 sFCell sFCell Direction.right 0
    , transition 0 sTCell sTCell Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 sFCell sFCell Direction.right 1
    , transition 1 sTCell sTCell Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 2
    , transition 2 sFCell sFCell Direction.right 3
    , transition 2 sTCell sTCell Direction.right 3
    , transition 3 sFCell sFCell Direction.right 3
    , transition 3 sTCell sTCell Direction.right 3
    , transition 3 none none Direction.left 4
    , transition 4 sFCell none Direction.left 5
    , transition 4 sTCell none Direction.left 6
    , transition 5 sFCell sFCell Direction.left 5
    , transition 5 sTCell sTCell Direction.left 5
    , transition 5 none none Direction.left 7
    , transition 6 sFCell sFCell Direction.left 6
    , transition 6 sTCell sTCell Direction.left 6
    , transition 6 none none Direction.left 8
    , transition 7 none none Direction.left 7
    , transition 7 sFCell sFCell Direction.left 9
    , transition 7 sTCell sTCell Direction.left 9
    , transition 8 none none Direction.left 8
    , transition 8 sFCell sFCell Direction.left 10
    , transition 8 sTCell sTCell Direction.left 10
    , transition 9 sFCell sFCell Direction.left 9
    , transition 9 sTCell sTCell Direction.left 9
    , transition 9 none none Direction.left 11
    , transition 10 sFCell sFCell Direction.left 10
    , transition 10 sTCell sTCell Direction.left 10
    , transition 10 none none Direction.left 12
    , transition 11 sFCell sFCell Direction.left 11
    , transition 11 sTCell sTCell Direction.left 11
    , transition 11 none sFCell Direction.left 13
    , transition 12 sFCell sFCell Direction.left 12
    , transition 12 sTCell sTCell Direction.left 12
    , transition 12 none sTCell Direction.left 13
    , transition 13 none none Direction.right 14 ]

/--
Looping pull across one interior run: repeatedly move the pulled field's
rightmost bit to the block's left edge until the field is exhausted (the
erased bit's left neighbor is blank), then park on the block's leftmost bit.
-/
def pullLoopJ1Description : MachineDescription where
  stateCount := 27
  start := 0
  halt := 26
  transitions :=
    [ transition 0 sFCell sFCell Direction.right 0
    , transition 0 sTCell sTCell Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 sFCell sFCell Direction.right 1
    , transition 1 sTCell sTCell Direction.right 1
    , transition 1 none none Direction.right 2
    , transition 2 none none Direction.right 2
    , transition 2 sFCell sFCell Direction.right 3
    , transition 2 sTCell sTCell Direction.right 3
    , transition 3 sFCell sFCell Direction.right 3
    , transition 3 sTCell sTCell Direction.right 3
    , transition 3 none none Direction.left 4
    , transition 4 sFCell none Direction.left 5
    , transition 4 sTCell none Direction.left 6
    , transition 5 sFCell sFCell Direction.left 7
    , transition 5 sTCell sTCell Direction.left 7
    , transition 5 none none Direction.left 19
    , transition 6 sFCell sFCell Direction.left 8
    , transition 6 sTCell sTCell Direction.left 8
    , transition 6 none none Direction.left 20
    , transition 7 sFCell sFCell Direction.left 7
    , transition 7 sTCell sTCell Direction.left 7
    , transition 7 none none Direction.left 9
    , transition 8 sFCell sFCell Direction.left 8
    , transition 8 sTCell sTCell Direction.left 8
    , transition 8 none none Direction.left 10
    , transition 9 none none Direction.left 9
    , transition 9 sFCell sFCell Direction.left 11
    , transition 9 sTCell sTCell Direction.left 11
    , transition 10 none none Direction.left 10
    , transition 10 sFCell sFCell Direction.left 12
    , transition 10 sTCell sTCell Direction.left 12
    , transition 11 sFCell sFCell Direction.left 11
    , transition 11 sTCell sTCell Direction.left 11
    , transition 11 none none Direction.left 13
    , transition 12 sFCell sFCell Direction.left 12
    , transition 12 sTCell sTCell Direction.left 12
    , transition 12 none none Direction.left 14
    , transition 13 sFCell sFCell Direction.left 13
    , transition 13 sTCell sTCell Direction.left 13
    , transition 13 none sFCell Direction.right 15
    , transition 14 sFCell sFCell Direction.left 14
    , transition 14 sTCell sTCell Direction.left 14
    , transition 14 none sTCell Direction.right 15
    , transition 15 sFCell sFCell Direction.right 15
    , transition 15 sTCell sTCell Direction.right 15
    , transition 15 none none Direction.right 16
    , transition 16 sFCell sFCell Direction.right 16
    , transition 16 sTCell sTCell Direction.right 16
    , transition 16 none none Direction.right 17
    , transition 17 none none Direction.right 17
    , transition 17 sFCell sFCell Direction.right 18
    , transition 17 sTCell sTCell Direction.right 18
    , transition 18 sFCell sFCell Direction.right 18
    , transition 18 sTCell sTCell Direction.right 18
    , transition 18 none none Direction.left 4
    , transition 19 none none Direction.left 19
    , transition 19 sFCell sFCell Direction.left 21
    , transition 19 sTCell sTCell Direction.left 21
    , transition 20 none none Direction.left 20
    , transition 20 sFCell sFCell Direction.left 22
    , transition 20 sTCell sTCell Direction.left 22
    , transition 21 sFCell sFCell Direction.left 21
    , transition 21 sTCell sTCell Direction.left 21
    , transition 21 none none Direction.left 23
    , transition 22 sFCell sFCell Direction.left 22
    , transition 22 sTCell sTCell Direction.left 22
    , transition 22 none none Direction.left 24
    , transition 23 sFCell sFCell Direction.left 23
    , transition 23 sTCell sTCell Direction.left 23
    , transition 23 none sFCell Direction.left 25
    , transition 24 sFCell sFCell Direction.left 24
    , transition 24 sTCell sTCell Direction.left 24
    , transition 24 none sTCell Direction.left 25
    , transition 25 none none Direction.right 26 ]

/-- Looping pull with the pulled field adjacent to the cell-0 sentinel. -/
def pullLoopJ0Description : MachineDescription where
  stateCount := 15
  start := 0
  halt := 14
  transitions :=
    [ transition 0 sFCell sFCell Direction.right 0
    , transition 0 sTCell sTCell Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 sFCell sFCell Direction.right 1
    , transition 1 sTCell sTCell Direction.right 1
    , transition 1 none none Direction.left 2
    , transition 2 sFCell none Direction.left 3
    , transition 2 sTCell none Direction.left 4
    , transition 3 sFCell sFCell Direction.left 5
    , transition 3 sTCell sTCell Direction.left 5
    , transition 3 none none Direction.left 11
    , transition 4 sFCell sFCell Direction.left 6
    , transition 4 sTCell sTCell Direction.left 6
    , transition 4 none none Direction.left 12
    , transition 5 sFCell sFCell Direction.left 5
    , transition 5 sTCell sTCell Direction.left 5
    , transition 5 none none Direction.left 7
    , transition 6 sFCell sFCell Direction.left 6
    , transition 6 sTCell sTCell Direction.left 6
    , transition 6 none none Direction.left 8
    , transition 7 sFCell sFCell Direction.left 7
    , transition 7 sTCell sTCell Direction.left 7
    , transition 7 none sFCell Direction.right 9
    , transition 8 sFCell sFCell Direction.left 8
    , transition 8 sTCell sTCell Direction.left 8
    , transition 8 none sTCell Direction.right 9
    , transition 9 sFCell sFCell Direction.right 9
    , transition 9 sTCell sTCell Direction.right 9
    , transition 9 none none Direction.right 10
    , transition 10 sFCell sFCell Direction.right 10
    , transition 10 sTCell sTCell Direction.right 10
    , transition 10 none none Direction.left 2
    , transition 11 sFCell sFCell Direction.left 11
    , transition 11 sTCell sTCell Direction.left 11
    , transition 11 none sFCell Direction.left 13
    , transition 12 sFCell sFCell Direction.left 12
    , transition 12 sTCell sTCell Direction.left 12
    , transition 12 none sTCell Direction.left 13
    , transition 13 none none Direction.right 14 ]

/-!
## Readiness trios
-/

theorem subroutineReady_of_checks {D : MachineDescription}
    (h0 : 0 < D.stateCount)
    (h1 : D.start < D.stateCount)
    (h2 : D.halt < D.stateCount)
    (h3 : D.transitions.all
      (transitionWellFormedBool D.stateCount) = true)
    (h4 : D.transitions.all (fun t =>
      D.transitions.all
        (fun u => transitionDeterministicPairBool t u)) = true)
    (h5 : D.transitions.all
      (transitionNotFromBool D.halt) = true) :
    D.SubroutineReady :=
  ⟨⟨h0, h1, h2,
      transition_wellFormed_of_all h3,
      transition_deterministic_of_all h4⟩,
    transition_notFrom_of_all h5⟩

theorem transportEntryDescription_subroutineReady :
    transportEntryDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem sentinelStashDescription_subroutineReady :
    sentinelStashDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem sentinelRestoreDescription_subroutineReady :
    sentinelRestoreDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem blankRightWalkerDescription_subroutineReady :
    blankRightWalkerDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem acceptMidEraserDescription_subroutineReady :
    acceptMidEraserDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem rejectMidEraserDescription_subroutineReady :
    rejectMidEraserDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pullFirstAcceptDescription_subroutineReady :
    pullFirstAcceptDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pullFirstRejectDescription_subroutineReady :
    pullFirstRejectDescription.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pullOneBitJ2Description_subroutineReady :
    pullOneBitJ2Description.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pullOneBitJ1Description_subroutineReady :
    pullOneBitJ1Description.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pullLoopJ1Description_subroutineReady :
    pullLoopJ1Description.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem pullLoopJ0Description_subroutineReady :
    pullLoopJ0Description.SubroutineReady :=
  subroutineReady_of_checks (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-!
## Generic run primitives

The transport machines are built almost entirely from four local motions:
crossing a bit run or a blank run in either direction, ending with a single
exit transition on the first cell of the following run.  The lemmas below
prove these motions once, parameterized by lookup facts, so each machine's
run lemma is a chain of instantiations.
-/

/-- One-sided view of a tape whose head cell and left context are listed
head-first going leftward. -/
def tapeSeenLeft (cells right : List (Option Bool)) : Tape Bool :=
  match cells with
  | [] => { left := [], head := none, right := right }
  | cell :: rest => { left := rest, head := cell, right := right }

@[simp] theorem tapeSeenLeft_cons
    (cell : Option Bool) (rest right : List (Option Bool)) :
    tapeSeenLeft (cell :: rest) right =
      { left := rest, head := cell, right := right } :=
  rfl

/-- Reachability in some number of steps. -/
def Reaches (D : MachineDescription) (a b : Configuration) : Prop :=
  exists n : Nat, D.runConfig n a = b

theorem Reaches.of_run {D : MachineDescription} {a b : Configuration}
    {n : Nat} (h : D.runConfig n a = b) : Reaches D a b :=
  ⟨n, h⟩

theorem Reaches.refl (D : MachineDescription) (a : Configuration) :
    Reaches D a a :=
  ⟨0, rfl⟩

theorem Reaches.trans {D : MachineDescription} {a b c : Configuration}
    (h1 : Reaches D a b) (h2 : Reaches D b c) : Reaches D a c := by
  rcases h1 with ⟨n, h1⟩
  rcases h2 with ⟨m, h2⟩
  exact ⟨n + m, by rw [MachineDescription.runConfig_add, h1, h2]⟩

theorem haltsFromTape_of_reaches {D : MachineDescription}
    {Tin Tout : Tape Bool}
    (h : Reaches D { state := D.start, tape := Tin }
      { state := D.halt, tape := Tout }) :
    D.HaltsFromTape Tin Tout := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, by
    constructor
    · simpa using congrArg Configuration.state hn
    · simpa using congrArg Configuration.tape hn⟩

theorem replicate_none_append_cons (n : Nat) (L : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: L) =
      List.append (List.replicate (n + 1) (none : Option Bool)) L := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, List.append_eq] at *
      rw [ih]

/-- Single step through a looked-up transition. -/
theorem runConfig_one {D : MachineDescription} {s : Nat}
    {read write : Option Bool} {dir : Direction} {t : Nat}
    (h : D.lookupTransition s read =
      some (transition s read write dir t))
    (T : Tape Bool) (hread : Tape.read T = read) :
    D.runConfig 1 { state := s, tape := T } =
      { state := t, tape := Tape.move dir (Tape.write write T) } := by
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hread, h, transition]

/-- Cross a bit run rightward on a self-looping state, then take the exit
transition on the blank that follows the run. -/
theorem runConfig_bitsRun_exitBlank_right
    {D : MachineDescription} {s : Nat}
    {w : Option Bool} {d : Direction} {t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right s))
    (hExit : D.lookupTransition s none =
      some (transition s none w d t))
    (bits : Word Bool) (L R : List (Option Bool)) :
    D.runConfig (bits.length + 1)
        { state := s
          tape := tapeAtCells L (List.append (bits.map some) (none :: R)) } =
      { state := t
        tape := Tape.move d (Tape.write w
          (tapeAtCells (List.append (bits.reverse.map some) L) (none :: R))) } := by
  induction bits generalizing L with
  | nil =>
      simpa [tapeAtCells] using
        runConfig_one hExit (tapeAtCells L (none :: R)) rfl
  | cons b rest ih =>
      have hstep :
          D.runConfig 1
              { state := s
                tape := tapeAtCells L
                  (List.append ((b :: rest).map some) (none :: R)) } =
            { state := s
              tape := tapeAtCells (some b :: L)
                (List.append (rest.map some) (none :: R)) } := by
        cases b <;> cases rest <;>
          simp [MachineDescription.runConfig, MachineDescription.stepConfig,
            hF, hT, transition,
            Tape.read, Tape.write, Tape.move, Tape.moveRight, tapeAtCells]
      have hlen : ((b :: rest) : Word Bool).length + 1 =
          1 + (rest.length + 1) := by
        simp [List.length_cons]
        lia
      rw [hlen, MachineDescription.runConfig_add, hstep, ih (some b :: L)]
      simp [List.append_assoc]

/-- Cross a blank run rightward on a self-looping state, then take the exit
transition (with write-back) on the first bit that follows. -/
theorem runConfig_blankRun_exitBit_right
    {D : MachineDescription} {s : Nat} {d : Direction} {t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.right s))
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) d t))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) d t))
    (n : Nat) (b : Bool) (L R : List (Option Bool)) :
    D.runConfig (n + 1)
        { state := s
          tape := tapeAtCells L
            (List.append (List.replicate n none) (some b :: R)) } =
      { state := t
        tape := Tape.move d (Tape.write (some b)
          (tapeAtCells (List.append (List.replicate n none) L)
            (some b :: R))) } := by
  induction n generalizing L with
  | zero =>
      cases b with
      | false =>
          simpa [tapeAtCells] using
            runConfig_one hF (tapeAtCells L (some false :: R)) rfl
      | true =>
          simpa [tapeAtCells] using
            runConfig_one hT (tapeAtCells L (some true :: R)) rfl
  | succ n ih =>
      have hstep :
          D.runConfig 1
              { state := s
                tape := tapeAtCells L
                  (List.append (List.replicate (n + 1) none) (some b :: R)) } =
            { state := s
              tape := tapeAtCells (none :: L)
                (List.append (List.replicate n none) (some b :: R)) } := by
        cases n <;>
          simp [MachineDescription.runConfig, MachineDescription.stepConfig,
            hN, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveRight, tapeAtCells, List.replicate_succ]
      have hlen : n + 1 + 1 = 1 + (n + 1) := by lia
      rw [hlen, MachineDescription.runConfig_add, hstep, ih (none :: L)]
      rw [replicate_none_append_cons]

/-- Cross a bit run leftward on a self-looping state, then take the exit
transition on the blank that follows the run to the left.  The run is given
in reversed (tape-left) order. -/
theorem runConfig_bitsRun_exitBlank_left
    {D : MachineDescription} {s : Nat}
    {w : Option Bool} {d : Direction} {t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none w d t))
    (revBits : Word Bool) (L R : List (Option Bool)) :
    D.runConfig (revBits.length + 1)
        { state := s
          tape := tapeSeenLeft
            (List.append (revBits.map some) (none :: L)) R } =
      { state := t
        tape := Tape.move d (Tape.write w
          (tapeSeenLeft (none :: L)
            (List.append (revBits.reverse.map some) R))) } := by
  induction revBits generalizing R with
  | nil =>
      simpa [tapeSeenLeft] using
        runConfig_one hExit (tapeSeenLeft (none :: L) R) rfl
  | cons b rest ih =>
      have hstep :
          D.runConfig 1
              { state := s
                tape := tapeSeenLeft
                  (List.append ((b :: rest).map some) (none :: L)) R } =
            { state := s
              tape := tapeSeenLeft
                (List.append (rest.map some) (none :: L)) (some b :: R) } := by
        cases b <;> cases rest <;>
          simp [MachineDescription.runConfig, MachineDescription.stepConfig,
            hF, hT, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, tapeSeenLeft]
      have hlen : ((b :: rest) : Word Bool).length + 1 =
          1 + (rest.length + 1) := by
        simp [List.length_cons]
        lia
      rw [hlen, MachineDescription.runConfig_add, hstep, ih (some b :: R)]
      simp [List.append_assoc]

/-- Cross a blank run leftward on a self-looping state, then take the exit
transition (with write-back) on the first bit to the left. -/
theorem runConfig_blankRun_exitBit_left
    {D : MachineDescription} {s : Nat} {d : Direction} {t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.left s))
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) d t))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) d t))
    (n : Nat) (b : Bool) (L R : List (Option Bool)) :
    D.runConfig (n + 1)
        { state := s
          tape := tapeSeenLeft
            (List.append (List.replicate n none) (some b :: L)) R } =
      { state := t
        tape := Tape.move d (Tape.write (some b)
          (tapeSeenLeft (some b :: L)
            (List.append (List.replicate n none) R))) } := by
  induction n generalizing R with
  | zero =>
      cases b with
      | false =>
          simpa [tapeSeenLeft] using
            runConfig_one hF (tapeSeenLeft (some false :: L) R) rfl
      | true =>
          simpa [tapeSeenLeft] using
            runConfig_one hT (tapeSeenLeft (some true :: L) R) rfl
  | succ n ih =>
      have hstep :
          D.runConfig 1
              { state := s
                tape := tapeSeenLeft
                  (List.append (List.replicate (n + 1) none) (some b :: L)) R } =
            { state := s
              tape := tapeSeenLeft
                (List.append (List.replicate n none) (some b :: L))
                (none :: R) } := by
        cases n <;>
          simp [MachineDescription.runConfig, MachineDescription.stepConfig,
            hN, transition, Tape.read, Tape.write, Tape.move,
            Tape.moveLeft, tapeSeenLeft, List.replicate_succ]
      have hlen : n + 1 + 1 = 1 + (n + 1) := by lia
      rw [hlen, MachineDescription.runConfig_add, hstep, ih (none :: R)]
      rw [replicate_none_append_cons]

/-- Cross a blank run rightward, hand over to a second self-looping state on
the first bit, cross the following bit run, and take the exit transition on
the blank after it. -/
theorem runConfig_blanksThenBits_exitBlank_right
    {D : MachineDescription} {s s2 : Nat}
    {w : Option Bool} {d : Direction} {t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.right s))
    (hSF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right s2))
    (hST : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right s2))
    (h2F : D.lookupTransition s2 (some false) =
      some (transition s2 (some false) (some false) Direction.right s2))
    (h2T : D.lookupTransition s2 (some true) =
      some (transition s2 (some true) (some true) Direction.right s2))
    (hExit : D.lookupTransition s2 none =
      some (transition s2 none w d t))
    (n : Nat) (W : Word Bool) (hW : W ≠ [])
    (L R : List (Option Bool)) :
    D.runConfig (n + W.length + 1)
        { state := s
          tape := tapeAtCells L
            (List.append (List.replicate n none)
              (List.append (W.map some) (none :: R))) } =
      { state := t
        tape := Tape.move d (Tape.write w
          (tapeAtCells
            (List.append (W.reverse.map some)
              (List.append (List.replicate n none) L))
            (none :: R))) } := by
  cases W with
  | nil => exact absurd rfl hW
  | cons w0 wT =>
      have h1 :
          D.runConfig (n + 1)
              { state := s
                tape := tapeAtCells L
                  (List.append (List.replicate n none)
                    (List.append ((w0 :: wT).map some) (none :: R))) } =
            { state := s2
              tape := tapeAtCells
                (some w0 :: List.append (List.replicate n none) L)
                (List.append (wT.map some) (none :: R)) } := by
        have := runConfig_blankRun_exitBit_right hN hSF hST n w0 L
          (List.append (wT.map some) (none :: R))
        cases wT <;>
          simpa [Tape.move, Tape.moveRight, Tape.write, tapeAtCells,
            List.append_assoc] using this
      have h2 :
          D.runConfig (wT.length + 1)
              { state := s2
                tape := tapeAtCells
                  (some w0 :: List.append (List.replicate n none) L)
                  (List.append (wT.map some) (none :: R)) } =
            { state := t
              tape := Tape.move d (Tape.write w
                (tapeAtCells
                  (List.append (wT.reverse.map some)
                    (some w0 :: List.append (List.replicate n none) L))
                  (none :: R))) } :=
        runConfig_bitsRun_exitBlank_right h2F h2T hExit wT _ R
      have hlen : n + (w0 :: wT).length + 1 =
          (n + 1) + (wT.length + 1) := by
        simp [List.length_cons]
        lia
      rw [hlen, MachineDescription.runConfig_add, h1, h2]
      simp [List.append_assoc]

/-- Cross a blank run leftward, hand over to a second self-looping state on
the first bit, cross the following bit run (given in reversed order), and
take the exit transition on the blank after it to the left. -/
theorem runConfig_blanksThenBitsRev_exitBlank_left
    {D : MachineDescription} {s s2 : Nat}
    {w : Option Bool} {d : Direction} {t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.left s))
    (hSF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s2))
    (hST : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s2))
    (h2F : D.lookupTransition s2 (some false) =
      some (transition s2 (some false) (some false) Direction.left s2))
    (h2T : D.lookupTransition s2 (some true) =
      some (transition s2 (some true) (some true) Direction.left s2))
    (hExit : D.lookupTransition s2 none =
      some (transition s2 none w d t))
    (n : Nat) (revW : Word Bool) (hW : revW ≠ [])
    (L R : List (Option Bool)) :
    D.runConfig (n + revW.length + 1)
        { state := s
          tape := tapeSeenLeft
            (List.append (List.replicate n none)
              (List.append (revW.map some) (none :: L))) R } =
      { state := t
        tape := Tape.move d (Tape.write w
          (tapeSeenLeft (none :: L)
            (List.append (revW.reverse.map some)
              (List.append (List.replicate n none) R)))) } := by
  cases revW with
  | nil => exact absurd rfl hW
  | cons w0 wT =>
      have h1 :
          D.runConfig (n + 1)
              { state := s
                tape := tapeSeenLeft
                  (List.append (List.replicate n none)
                    (List.append ((w0 :: wT).map some) (none :: L))) R } =
            { state := s2
              tape := tapeSeenLeft
                (List.append (wT.map some) (none :: L))
                (some w0 :: List.append (List.replicate n none) R) } := by
        have := runConfig_blankRun_exitBit_left hN hSF hST n w0
          (List.append (wT.map some) (none :: L)) R
        cases wT <;>
          simpa [Tape.move, Tape.moveLeft, Tape.write, tapeSeenLeft,
            List.append_assoc] using this
      have h2 :
          D.runConfig (wT.length + 1)
              { state := s2
                tape := tapeSeenLeft
                  (List.append (wT.map some) (none :: L))
                  (some w0 :: List.append (List.replicate n none) R) } =
            { state := t
              tape := Tape.move d (Tape.write w
                (tapeSeenLeft (none :: L)
                  (List.append (wT.reverse.map some)
                    (some w0 :: List.append (List.replicate n none) R)))) } :=
        runConfig_bitsRun_exitBlank_left h2F h2T hExit wT L _
      have hlen : n + (w0 :: wT).length + 1 =
          (n + 1) + (wT.length + 1) := by
        simp [List.length_cons]
        lia
      rw [hlen, MachineDescription.runConfig_add, h1, h2]
      simp [List.append_assoc]

/-!
## Normalized crossing corollaries

The general crossing lemmas end in a pending {lit}`move`/{lit}`write`; the
corollaries below normalize those endings to {name}`tapeAtCells` and
{name}`tapeSeenLeft` forms for the exit shapes the transport machines actually
use, so machine run lemmas chain without per-step tape surgery.
-/

theorem move_right_write_tapeAtCells
    (L R : List (Option Bool)) (h w : Option Bool) :
    Tape.move Direction.right (Tape.write w (tapeAtCells L (h :: R))) =
      tapeAtCells (w :: L) R := by
  cases R <;> rfl

theorem move_left_write_tapeAtCells
    (L R : List (Option Bool)) (h w : Option Bool) :
    Tape.move Direction.left (Tape.write w (tapeAtCells L (h :: R))) =
      tapeSeenLeft L (w :: R) := by
  cases L <;> rfl

theorem move_left_write_tapeSeenLeft
    (L R : List (Option Bool)) (h w : Option Bool) :
    Tape.move Direction.left (Tape.write w (tapeSeenLeft (h :: L) R)) =
      tapeSeenLeft L (w :: R) := by
  cases L <;> rfl

theorem move_right_write_tapeSeenLeft
    (L R : List (Option Bool)) (h w : Option Bool) :
    Tape.move Direction.right (Tape.write w (tapeSeenLeft (h :: L) R)) =
      tapeAtCells (w :: L) R := by
  cases R <;> rfl

/-- Bit-run crossing rightward whose exit steps right over the blank. -/
theorem crossBitsRightThenRight
    {D : MachineDescription} {s t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right s))
    (hExit : D.lookupTransition s none =
      some (transition s none none Direction.right t))
    (bits : Word Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeAtCells L (List.append (bits.map some) (none :: R)) }
      { state := t
        tape := tapeAtCells
          (none :: List.append (bits.reverse.map some) L) R } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_right hF hT hExit bits L R
    rwa [move_right_write_tapeAtCells] at this)

/-- Blank-run-then-bit-run crossing rightward whose exit steps right. -/
theorem crossBlanksBitsRightThenRight
    {D : MachineDescription} {s s2 t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.right s))
    (hSF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right s2))
    (hST : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right s2))
    (h2F : D.lookupTransition s2 (some false) =
      some (transition s2 (some false) (some false) Direction.right s2))
    (h2T : D.lookupTransition s2 (some true) =
      some (transition s2 (some true) (some true) Direction.right s2))
    (hExit : D.lookupTransition s2 none =
      some (transition s2 none none Direction.right t))
    (n : Nat) (W : Word Bool) (hW : W ≠ [])
    (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeAtCells L
          (List.append (List.replicate n none)
            (List.append (W.map some) (none :: R))) }
      { state := t
        tape := tapeAtCells
          (none :: List.append (W.reverse.map some)
            (List.append (List.replicate n none) L)) R } :=
  Reaches.of_run (by
    have := runConfig_blanksThenBits_exitBlank_right
      hN hSF hST h2F h2T hExit n W hW L R
    rwa [move_right_write_tapeAtCells] at this)

/-- Blank-run-then-bit-run crossing rightward whose exit steps back left. -/
theorem crossBlanksBitsRightThenLeft
    {D : MachineDescription} {s s2 t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.right s))
    (hSF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.right s2))
    (hST : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.right s2))
    (h2F : D.lookupTransition s2 (some false) =
      some (transition s2 (some false) (some false) Direction.right s2))
    (h2T : D.lookupTransition s2 (some true) =
      some (transition s2 (some true) (some true) Direction.right s2))
    (hExit : D.lookupTransition s2 none =
      some (transition s2 none none Direction.left t))
    (n : Nat) (W : Word Bool) (hW : W ≠ [])
    (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeAtCells L
          (List.append (List.replicate n none)
            (List.append (W.map some) (none :: R))) }
      { state := t
        tape := tapeSeenLeft
          (List.append (W.reverse.map some)
            (List.append (List.replicate n none) L)) (none :: R) } :=
  Reaches.of_run (by
    have := runConfig_blanksThenBits_exitBlank_right
      hN hSF hST h2F h2T hExit n W hW L R
    rwa [move_left_write_tapeAtCells] at this)

/-- Pull step: erase the carried bit and step left. -/
theorem pullStepLeft
    {D : MachineDescription} {s t : Nat} {x : Bool}
    (h : D.lookupTransition s (some x) =
      some (transition s (some x) none Direction.left t))
    (L R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (some x :: L) R }
      { state := t, tape := tapeSeenLeft L (none :: R) } :=
  Reaches.of_run (by
    have := runConfig_one h (tapeSeenLeft (some x :: L) R)
      (by cases L <;> rfl)
    rwa [move_left_write_tapeSeenLeft] at this)

/-- Bit-run crossing leftward whose exit steps left over the blank. -/
theorem crossBitsLeftThenLeft
    {D : MachineDescription} {s t : Nat}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none none Direction.left t))
    (revBits : Word Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeSeenLeft
          (List.append (revBits.map some) (none :: L)) R }
      { state := t
        tape := tapeSeenLeft L
          (none :: List.append (revBits.reverse.map some) R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_left hF hT hExit revBits L R
    rwa [move_left_write_tapeSeenLeft] at this)

/-- Blank-run-then-bit-run crossing leftward whose exit steps left. -/
theorem crossBlanksBitsLeftThenLeft
    {D : MachineDescription} {s s2 t : Nat}
    (hN : D.lookupTransition s none =
      some (transition s none none Direction.left s))
    (hSF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s2))
    (hST : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s2))
    (h2F : D.lookupTransition s2 (some false) =
      some (transition s2 (some false) (some false) Direction.left s2))
    (h2T : D.lookupTransition s2 (some true) =
      some (transition s2 (some true) (some true) Direction.left s2))
    (hExit : D.lookupTransition s2 none =
      some (transition s2 none none Direction.left t))
    (n : Nat) (revW : Word Bool) (hW : revW ≠ [])
    (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeSeenLeft
          (List.append (List.replicate n none)
            (List.append (revW.map some) (none :: L))) R }
      { state := t
        tape := tapeSeenLeft L
          (none :: List.append (revW.reverse.map some)
            (List.append (List.replicate n none) R)) } :=
  Reaches.of_run (by
    have := runConfig_blanksThenBitsRev_exitBlank_left
      hN hSF hST h2F h2T hExit n revW hW L R
    rwa [move_left_write_tapeSeenLeft] at this)

/-- Bit-run crossing leftward that delivers the carried bit on the blank
past the run and steps further left. -/
theorem deliverLeft
    {D : MachineDescription} {s t : Nat} {x : Bool}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none (some x) Direction.left t))
    (revBits : Word Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeSeenLeft
          (List.append (revBits.map some) (none :: L)) R }
      { state := t
        tape := tapeSeenLeft L
          (some x :: List.append (revBits.reverse.map some) R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_left hF hT hExit revBits L R
    rwa [move_left_write_tapeSeenLeft] at this)

/-- Bit-run crossing leftward that delivers the carried bit on the blank
past the run and steps back right onto the old block. -/
theorem deliverRight
    {D : MachineDescription} {s t : Nat} {x : Bool}
    (hF : D.lookupTransition s (some false) =
      some (transition s (some false) (some false) Direction.left s))
    (hT : D.lookupTransition s (some true) =
      some (transition s (some true) (some true) Direction.left s))
    (hExit : D.lookupTransition s none =
      some (transition s none (some x) Direction.right t))
    (revBits : Word Bool) (L R : List (Option Bool)) :
    Reaches D
      { state := s
        tape := tapeSeenLeft
          (List.append (revBits.map some) (none :: L)) R }
      { state := t
        tape := tapeAtCells (some x :: L)
          (List.append (revBits.reverse.map some) R) } :=
  Reaches.of_run (by
    have := runConfig_bitsRun_exitBlank_left hF hT hExit revBits L R
    rwa [move_right_write_tapeSeenLeft] at this)

/-- Final parking step: on a blank with the block to the right, write back
and step right onto the block's first bit. -/
theorem parkRight
    {D : MachineDescription} {s t : Nat}
    (h : D.lookupTransition s none =
      some (transition s none none Direction.right t))
    (L R : List (Option Bool)) :
    Reaches D
      { state := s, tape := tapeSeenLeft (none :: L) R }
      { state := t, tape := tapeAtCells (none :: L) R } :=
  Reaches.of_run (by
    have := runConfig_one h (tapeSeenLeft (none :: L) R)
      (by cases L <;> rfl)
    rwa [move_right_write_tapeSeenLeft] at this)

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC

import FoC.Foundation.Reals.BasicPart2

set_option doc.verso true

/-!
# Basic

Re-export wrapper: importing this module provides the whole Dedekind-cut
real-number development. The cut, order, addition, negation, and nonnegative
multiplication core lives in {module}`FoC.Foundation.Reals.BasicPart1`.
The remaining implementation is organized by subject in
{module}`FoC.Foundation.Reals.Multiplication`,
{module}`FoC.Foundation.Reals.Division`,
{module}`FoC.Foundation.Reals.SquareRoots`, and
{module}`FoC.Foundation.Reals.Density`. The
{module}`FoC.Foundation.Reals.BasicPart2` module remains as a compatibility
import for existing clients.
-/

import FoC.Book.Chapter04.Section01.Basic
import FoC.Book.Chapter04.Section01.Closure
import FoC.Book.Chapter04.Section01.Common
import FoC.Book.Chapter04.Section01.BalancedParentheses
import FoC.Book.Chapter04.Section01.BalancedBrackets
import FoC.Book.Chapter04.Section01.AnBn
import FoC.Book.Chapter04.Section01.Palindromes

set_option doc.verso true

/-!
# Chapter 4, Section 4.1: Context-Free Grammars

This facade exposes the chapter-facing derivation laws, language classes,
closure theorems, and exact concrete grammars through semantic child modules.
Reusable grammar machinery remains under {module -checked}`FoC.Grammars`; the child
modules here preserve the textbook's examples and theorem names.

The strict regular/context-free boundary is kept in the independent
{module -checked}`FoC.Book.Chapter04.Section01.RegularBoundary` module because it also
depends on Chapter 3's pumping development.
-/

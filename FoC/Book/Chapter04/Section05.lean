import FoC.Book.Chapter04.Section05.Basic

set_option doc.verso true

/-!
# Chapter 4, Section 4.5: Context-Free Pumping and Nonclosure

This wrapper exposes the chapter-facing context-free pumping and nonclosure
material. The child module packages the reusable CFL pumping lemma, the
complete non-context-freeness proof for {lit}`a^n b^n c^n`, the counting core of
the argument for the duplicate-word language {lit}`w w` (the all-{lit}`a`
pumping case is left to the book's position argument), and the closure or
nonclosure consequences used by the book narrative.
-/

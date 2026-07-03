import FoC.Grammars.ParseTreePart2

set_option doc.verso true

/-!
# ParseTree

This wrapper exposes the reusable parse-tree API for Chapter 4. The split
modules connect trees to generated-language membership, frontiers, leftmost
derivations, ambiguity witnesses, height bounds, repeated nonterminals, and the
subtree machinery used by the context-free pumping argument.

Read this module when the chapter-facing theorem mentions parse trees but the
proof needs the derivation or pumping support hidden in the implementation
parts.
-/

import FoC.Book.Chapter04.Section01.AnBn
import FoC.Grammars.PDA

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# Shared Data for the Chapter 4 PDA Examples

The block-language examples use the same binary input alphabet, one-symbol
stack alphabet, and repeated-block notation. Keeping those definitions here
lets the individual machines remain independent siblings rather than forming
an artificial import chain.
-/

inductive AnBnPDAStack where
  | marker
deriving DecidableEq

namespace AnBnPDAStack

def finite : Foundation.FiniteType AnBnPDAStack where
  elems := [marker]
  complete := by
    intro symbol
    cases symbol
    simp

end AnBnPDAStack

def AnBnPDAStackWord (n : Nat) : Word AnBnPDAStack :=
  Word.RepeatSymbol AnBnPDAStack.marker n

theorem anbnPDAStackWord_succ (n : Nat) :
    AnBnPDAStack.marker :: AnBnPDAStackWord n =
      AnBnPDAStackWord (n + 1) :=
  rfl

def AnBmWord (n m : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a n)
    (Word.RepeatSymbol Section01.AB.b m)

end Section04
end Chapter04
end Book
end FoC

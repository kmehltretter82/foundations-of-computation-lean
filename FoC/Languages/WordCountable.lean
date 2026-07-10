import FoC.Foundation.Countable
import FoC.Languages.Words

set_option doc.verso true

/-!
# Countability of words

Finite words over a finite alphabet form a countable type.  When the alphabet
contains a symbol, words of increasing lengths also show that the type is not
finite, so its universal set is countably infinite.
-/

namespace FoC
namespace Languages

open Foundation

namespace Word

/-- Words over an explicitly finite alphabet inject into the natural numbers. -/
theorem encodableByNat (alphabet : FiniteType alpha) :
    Countability.EncodableByNat (Word alpha) :=
  Countability.list_encodable
    (Countability.finiteType_encodableByNat alphabet)

/-- The universal set of words over a finite alphabet is countable. -/
theorem univ_countable (alphabet : FiniteType alpha) :
    FSet.Countable (FSet.Univ : FSet (Word alpha)) :=
  Countability.countable_univ_of_encodableByNat (encodableByNat alphabet)

/-- If the alphabet has a symbol, its universal word set is not finite. -/
theorem univ_not_finite (a : alpha) :
    ¬ FSet.Finite (FSet.Univ : FSet (Word alpha)) := by
  intro hfinite
  rcases hfinite with ⟨words, hwords⟩
  let lengths := words.map Word.Length
  let n := lengths.foldr Nat.max 0 + 1
  let w := Word.RepeatSymbol a n
  have hw : w ∈ words := (hwords w).mp True.intro
  have hn : n ∈ lengths := by
    exact List.mem_map.mpr ⟨w, hw, Word.length_repeatSymbol a n⟩
  have hle := FSet.list_mem_le_foldr_max lengths n hn
  simp [n] at hle
  lia

/-- Words over a finite nonempty alphabet form a countably infinite set. -/
theorem univ_countablyInfinite (alphabet : FiniteType alpha) (a : alpha) :
    FSet.CountablyInfinite (FSet.Univ : FSet (Word alpha)) :=
  ⟨univ_countable alphabet, univ_not_finite a⟩

end Word
end Languages
end FoC

import FoC.Computability.Undecidable

set_option doc.verso true

/-!
# Concrete coding helpers

This module records concrete word encodings used by the Chapter 5
undecidability layer.  The constructions here are syntactic: they give
explicit words and prove their decoding properties without assuming an
interpreter or universal machine.

## Book coordinates

Used by:
- Chapter 5, Section 5.3: pair encodings for halting-problem reductions.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

/-!
# Pair codes

A pair is encoded by tagging the symbols from the left and right components.
The separator is included to mirror the textbook notation, but injectivity is
proved by projecting the tagged left and right symbols back out of the word.
-/

inductive PairCodeSymbol (code : Type u) where
  | left : code -> PairCodeSymbol code
  | separator : PairCodeSymbol code
  | right : code -> PairCodeSymbol code
deriving DecidableEq

namespace PairCodeSymbol

def finite (h : FiniteType code) : FiniteType (PairCodeSymbol code) where
  elems := h.elems.map PairCodeSymbol.left ++
    [PairCodeSymbol.separator] ++ h.elems.map PairCodeSymbol.right
  complete := by
    intro symbol
    cases symbol with
    | left c =>
        simp [h.complete c]
    | separator =>
        simp
    | right c =>
        simp [h.complete c]

def encodePair (left right : Word code) : Word (PairCodeSymbol code) :=
  List.append (List.append (left.map PairCodeSymbol.left)
    [PairCodeSymbol.separator]) (right.map PairCodeSymbol.right)

def diagonalMap (w : Word code) : Word (PairCodeSymbol code) :=
  encodePair w w

def leftComponent? : PairCodeSymbol code -> Option code
  | PairCodeSymbol.left c => some c
  | PairCodeSymbol.separator => none
  | PairCodeSymbol.right _ => none

def rightComponent? : PairCodeSymbol code -> Option code
  | PairCodeSymbol.left _ => none
  | PairCodeSymbol.separator => none
  | PairCodeSymbol.right c => some c

def leftProjection (w : Word (PairCodeSymbol code)) : Word code :=
  w.filterMap leftComponent?

def rightProjection (w : Word (PairCodeSymbol code)) : Word code :=
  w.filterMap rightComponent?

theorem leftProjection_append
    (x y : Word (PairCodeSymbol code)) :
    leftProjection (List.append x y) =
      List.append (leftProjection x) (leftProjection y) := by
  simp [leftProjection]

theorem rightProjection_append
    (x y : Word (PairCodeSymbol code)) :
    rightProjection (List.append x y) =
      List.append (rightProjection x) (rightProjection y) := by
  simp [rightProjection]

theorem leftProjection_left_map (w : Word code) :
    leftProjection (w.map PairCodeSymbol.left) = w := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
      change c :: leftProjection (rest.map PairCodeSymbol.left) = c :: rest
      rw [ih]

theorem leftProjection_right_map (w : Word code) :
    leftProjection (w.map PairCodeSymbol.right) = [] := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
      change leftProjection (rest.map PairCodeSymbol.right) = []
      exact ih

theorem rightProjection_left_map (w : Word code) :
    rightProjection (w.map PairCodeSymbol.left) = [] := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
      change rightProjection (rest.map PairCodeSymbol.left) = []
      exact ih

theorem rightProjection_right_map (w : Word code) :
    rightProjection (w.map PairCodeSymbol.right) = w := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
      change c :: rightProjection (rest.map PairCodeSymbol.right) = c :: rest
      rw [ih]

theorem leftProjection_encodePair (left right : Word code) :
    leftProjection (encodePair left right) = left := by
  change
    leftProjection
      (List.append
        (List.append (left.map PairCodeSymbol.left)
          [PairCodeSymbol.separator])
        (right.map PairCodeSymbol.right)) = left
  rw [leftProjection_append, leftProjection_append,
    leftProjection_left_map, leftProjection_right_map]
  simp [leftProjection, leftComponent?]

theorem rightProjection_encodePair (left right : Word code) :
    rightProjection (encodePair left right) = right := by
  change
    rightProjection
      (List.append
        (List.append (left.map PairCodeSymbol.left)
          [PairCodeSymbol.separator])
        (right.map PairCodeSymbol.right)) = right
  rw [rightProjection_append, rightProjection_append,
    rightProjection_left_map, rightProjection_right_map]
  simp [rightProjection, rightComponent?]

theorem encodePair_injective :
    PairEncodingInjective (encodePair : Word code -> Word code ->
      Word (PairCodeSymbol code)) := by
  intro a b c d h
  constructor
  · have hleft := congrArg leftProjection h
    simpa [leftProjection_encodePair] using hleft
  · have hright := congrArg rightProjection h
    simpa [rightProjection_encodePair] using hright

theorem diagonalMap_eq_diagonalPairMap :
    diagonalMap = DiagonalPairMap
      (encodePair : Word code -> Word code -> Word (PairCodeSymbol code)) :=
  rfl

theorem diagonalMap_preimage_pairHalting_equal_selfHalting
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    Language.Equal
      (WordPreimageLanguage
        (diagonalMap : Word code -> Word (PairCodeSymbol code))
        (PairHaltingProblem
          (encodePair : Word code -> Word code -> Word (PairCodeSymbol code))
          haltsOnCodeInput))
      (SelfHaltingLanguage haltsOnCodeInput) :=
  diagonalPairMap_preimage_pairHalting_equal_selfHalting
    (encodePair := encodePair)
    (haltsOnCodeInput := haltsOnCodeInput)
    encodePair_injective

theorem diagonalPairDecidablePreimagePrinciple_of_concrete_preimage
    (hpreimage : DecidablePreimagePrinciple
      (diagonalMap : Word code -> Word (PairCodeSymbol code))) :
    DiagonalPairDecidablePreimagePrinciple
      (encodePair : Word code -> Word code -> Word (PairCodeSymbol code)) := by
  rw [diagonalMap_eq_diagonalPairMap] at hpreimage
  exact diagonalPairDecidablePreimagePrinciple_of_preimage
    encodePair_injective hpreimage

theorem diagonalPairDecidablePreimagePrinciple_of_concrete_computable_map
    (hpreimage :
      ComputableMapDecidablePreimagePrinciple code (PairCodeSymbol code))
    (hcomputable :
      TuringComputable
        (diagonalMap : Word code -> Word (PairCodeSymbol code))) :
    DiagonalPairDecidablePreimagePrinciple
      (encodePair : Word code -> Word code -> Word (PairCodeSymbol code)) := by
  rw [diagonalMap_eq_diagonalPairMap] at hcomputable
  exact diagonalPairDecidablePreimagePrinciple_of_computableMapPrinciple
    encodePair_injective hpreimage hcomputable

theorem concretePairHalting_undecidable_if_decoder_universal_of_preimage
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (hpreimage : DecidablePreimagePrinciple
      (diagonalMap : Word code -> Word (PairCodeSymbol code)))
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableLanguage
      (PairHaltingProblem
        (encodePair : Word code -> Word code -> Word (PairCodeSymbol code))
        decodeAccepts) :=
  pairHalting_undecidable_if_decoder_universal
    haccept
    (diagonalPairDecidablePreimagePrinciple_of_concrete_preimage hpreimage)
    huniv

theorem concretePairHalting_undecidable_if_decoder_universal_of_computable_map
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (hpreimage :
      ComputableMapDecidablePreimagePrinciple code (PairCodeSymbol code))
    (hcomputable :
      TuringComputable
        (diagonalMap : Word code -> Word (PairCodeSymbol code)))
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableLanguage
      (PairHaltingProblem
        (encodePair : Word code -> Word code -> Word (PairCodeSymbol code))
        decodeAccepts) :=
  pairHalting_undecidable_if_decoder_universal
    haccept
    (diagonalPairDecidablePreimagePrinciple_of_concrete_computable_map
      hpreimage hcomputable)
    huniv

end PairCodeSymbol

end Computability
end FoC

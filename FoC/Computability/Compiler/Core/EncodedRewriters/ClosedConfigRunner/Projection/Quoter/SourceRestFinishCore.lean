import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.ScanRightToBlankLeft

set_option doc.verso true

/-!
# Source-rest finish core

This module records the exact tape and bit views for the final source-rest
finishing phase of the selected projection input quoter.  The phase starts
after the assembly scanner has parsed the {lit}`transition` field and the
stage-input prefix.  At that point the tape still contains a mixed parser-stack
layout: ordinary data cells are interleaved with parser {lit}`none` markers, and
the physical source-rest suffix remains live on the right.

The target tape has a fresh {lit}`header` length field, the quoted parser-stack
and stage-prefix bits, the quoted source-rest field, and the live tail named by
{lit}`assemblySourceRestFinishRawTailBits`.  The lemmas below keep these
pieces separate so the finite copier can distinguish structural markers from
payload cells while still quoting markers with {lit}`optionBitDefaultFalse`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
**Source and target bit views.**  These definitions name the raw source field,
the parsed source prefix, the emitted header/quote prefix, and the final live
tail.  Later proofs use these names instead of repeatedly expanding the nested
encoding append structure.
-/

def assemblySourceRestFinishSourceBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (List.append
      (DovetailInitialLayoutInitializer.stageInputBits w stage)
      sourceRestBits)

def assemblySourceRestFinishSourcePrefixBits
    (w : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (DovetailInitialLayoutInitializer.stageInputBits w stage)

def assemblySourceRestFinishTargetPrefixBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.header)
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
      (preservingCellPassCellBits
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)))

def assemblySourceRestFinishRawSourceBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  assemblySourceRestFinishSourceBits w sourceRestBits stage

def assemblySourceRestFinishRawTailBits
    (sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      stage)
    sourceRestBits

def assemblySourceRestFinishQuotedPrefixBits
    (w : Word Bool) (stage : Nat) : Word Bool :=
  preservingCellPassCellBits
    (assemblySourceRestFinishSourcePrefixBits w stage)

def assemblySourceRestFinishLengthHeaderBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.header)
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      ((assemblySourceRestFinishSourcePrefixBits w stage).length +
        sourceRestBits.length))

def assemblySourceRestFinishPrefixQuoteOutputBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (assemblySourceRestFinishLengthHeaderBits w sourceRestBits stage)
    (assemblySourceRestFinishQuotedPrefixBits w stage)

def assemblySourceRestFinishTargetBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (assemblySourceRestFinishPrefixQuoteOutputBits
      w sourceRestBits stage)
    (List.append
      (preservingCellPassCellBits sourceRestBits)
      (assemblySourceRestFinishRawTailBits sourceRestBits stage))

theorem assemblySourceRestFinishSourceBits_eq
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSourceBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits w stage)
          sourceRestBits) := by
  rfl

theorem assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSourceBits w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        sourceRestBits := by
  simp [assemblySourceRestFinishSourceBits,
    assemblySourceRestFinishSourcePrefixBits, List.append_assoc]

theorem assemblySourceRestFinishRawSourceBits_eq_prefix_append_sourceRest
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishRawSourceBits w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        sourceRestBits := by
  rw [assemblySourceRestFinishRawSourceBits,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]

theorem assemblySourceRestFinishSourcePrefixBits_eq_fields
    (w : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSourcePrefixBits w stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (DovetailInitialLayoutInitializer.stageInputBits w stage) := by
  rfl

theorem assemblySourceRestBoundaryLeftRev_defaultBits_eq_sourcePrefix
    (w : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage)) =
      assemblySourceRestFinishSourcePrefixBits w stage := by
  rw [assemblySourceRestBoundaryLeftRev_defaultBits,
    assemblySourceRestFinishSourcePrefixBits]

/-!
**Mixed parser-stack cells.**  The boundary scanner leaves the parsed prefix in
the same physical cell layout that the parser used.  The {lit}`none` separator
inside {lit}`assemblySourceRestFinishParserPrefixCells` is data for this
phase, not the blank that ends the source-rest field, so the split lemmas below
name the marker explicitly.
-/

def assemblySourceRestFinishParserStackCells
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  List.reverse (assemblySourceRestBoundaryLeftRev w stage)

def assemblySourceRestFinishFlatSourceCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List (Option Bool) :=
  List.append
    (assemblySourceRestFinishParserStackCells w stage)
    (sourceRestBits.map some)

def assemblySourceRestFinishQuoteRestCells
    (sourceRestBits : Word Bool) : List (Option Bool) :=
  (preservingCellPassCellBits sourceRestBits).map some

def assemblySourceRestFinishParserPrefixCells
    (w : Word Bool) : List (Option Bool) :=
  match w with
  | [] =>
      List.append
        (List.reverse transitionPrefixLeftTail)
        [some false, none, some true, some true]
  | b :: rest =>
      List.append
        (List.reverse transitionPrefixLeftTail)
        (List.append [some false, none]
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
            (b :: rest)).map some))

def assemblySourceRestFinishParserMarkerLeftCells :
    List (Option Bool) :=
  List.append (List.reverse transitionPrefixLeftTail) [some false]

def assemblySourceRestFinishParserMarkerRightCells
    (w : Word Bool) : List (Option Bool) :=
  match w with
  | [] => [some true, some true]
  | b :: rest =>
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        (b :: rest)).map some

def assemblySourceRestFinishParserMarkerRightBits
    (w : Word Bool) : Word Bool :=
  match w with
  | [] => [true, true]
  | b :: rest =>
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        (b :: rest)

theorem assemblySourceRestFinishParserMarkerRightCells_eq_bits
    (w : Word Bool) :
    assemblySourceRestFinishParserMarkerRightCells w =
      (assemblySourceRestFinishParserMarkerRightBits w).map some := by
  cases w with
  | nil =>
      rfl
  | cons b rest =>
      rfl

theorem assemblySourceRestFinishParserMarkerRightBits_nil :
    assemblySourceRestFinishParserMarkerRightBits ([] : Word Bool) =
      [true, true] := by
  rfl

theorem assemblySourceRestFinishParserMarkerRightBits_cons
    (b : Bool) (rest : Word Bool) :
    assemblySourceRestFinishParserMarkerRightBits (b :: rest) =
      true :: false ::
        List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            rest.length)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
              b)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest)) := by
  rfl

theorem assemblySourceRestFinishParserStackCells_nil_eq_segments
    (stage : Nat) :
    assemblySourceRestFinishParserStackCells ([] : Word Bool) stage =
      List.append
        (List.reverse transitionPrefixLeftTail)
        (List.append [some false, none, some true, some true]
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)) := by
  simp [assemblySourceRestFinishParserStackCells,
    assemblySourceRestBoundaryLeftRev, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishParserStackCells_cons_eq_segments
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    assemblySourceRestFinishParserStackCells (b :: rest) stage =
      List.append
        (List.reverse transitionPrefixLeftTail)
        (List.append [some false, none]
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).map some)
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some))) := by
  simp [assemblySourceRestFinishParserStackCells,
    assemblySourceRestBoundaryLeftRev, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishParserPrefixCells_nil
    :
    assemblySourceRestFinishParserPrefixCells ([] : Word Bool) =
      List.append
        (List.reverse transitionPrefixLeftTail)
        [some false, none, some true, some true] := by
  rfl

theorem assemblySourceRestFinishParserPrefixCells_cons
    (b : Bool) (rest : Word Bool) :
    assemblySourceRestFinishParserPrefixCells (b :: rest) =
      List.append
        (List.reverse transitionPrefixLeftTail)
        (List.append [some false, none]
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
            (b :: rest)).map some)) := by
  rfl

theorem assemblySourceRestFinishParserStackCells_defaultBits
    (w : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (assemblySourceRestFinishParserStackCells w stage) =
      assemblySourceRestFinishSourcePrefixBits w stage := by
  rw [assemblySourceRestFinishParserStackCells,
    assemblySourceRestBoundaryLeftRev_defaultBits_eq_sourcePrefix]

theorem assemblySourceRestFinishFlatSourceCells_defaultBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (assemblySourceRestFinishFlatSourceCells w sourceRestBits stage) =
      assemblySourceRestFinishSourceBits w sourceRestBits stage := by
  simp [assemblySourceRestFinishFlatSourceCells,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest,
    List.map_append, List.map_map,
    assemblySourceRestFinishParserStackCells_defaultBits,
    optionBitDefaultFalse_map_some]

theorem assemblySourceRestFinishQuoteRestCells_defaultBits
    (sourceRestBits : Word Bool) :
    List.map optionBitDefaultFalse
        (assemblySourceRestFinishQuoteRestCells sourceRestBits) =
      preservingCellPassCellBits sourceRestBits := by
  simp [assemblySourceRestFinishQuoteRestCells, List.map_map,
    optionBitDefaultFalse_map_some]

theorem assemblySourceRestFinishParserStackCells_eq_prefix_append_stageNat
    (w : Word Bool) (stage : Nat) :
    exists prefixCells : List (Option Bool),
      assemblySourceRestFinishParserStackCells w stage =
        List.append prefixCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some) := by
  cases w with
  | nil =>
      refine
        ⟨List.append
          (List.reverse transitionPrefixLeftTail)
          [some false, none, some true, some true], ?_⟩
      rw [assemblySourceRestFinishParserStackCells_nil_eq_segments]
      simp [List.append_assoc]
  | cons b rest =>
      refine
        ⟨List.append
          (List.reverse transitionPrefixLeftTail)
          (List.append [some false, none]
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).map some)), ?_⟩
      rw [assemblySourceRestFinishParserStackCells_cons_eq_segments]
      simp [List.append_assoc]

theorem assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat
    (w : Word Bool) (stage : Nat) :
    assemblySourceRestFinishParserStackCells w stage =
      List.append
        (assemblySourceRestFinishParserPrefixCells w)
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage).map some) := by
  cases w with
  | nil =>
      rw [assemblySourceRestFinishParserStackCells_nil_eq_segments]
      rfl
  | cons b rest =>
      rw [assemblySourceRestFinishParserStackCells_cons_eq_segments]
      rfl

theorem assemblySourceRestFinishParserPrefixCells_eq_marker_split
    (w : Word Bool) :
    assemblySourceRestFinishParserPrefixCells w =
      List.append
        assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          assemblySourceRestFinishParserMarkerRightCells w) := by
  cases w with
  | nil =>
      simp [assemblySourceRestFinishParserPrefixCells,
        assemblySourceRestFinishParserMarkerLeftCells,
        assemblySourceRestFinishParserMarkerRightCells,
        List.append_assoc]
  | cons b rest =>
      simp [assemblySourceRestFinishParserPrefixCells,
        assemblySourceRestFinishParserMarkerLeftCells,
        assemblySourceRestFinishParserMarkerRightCells,
        List.append_assoc]

/-!
**Abstract mixed rewriter layout.**  These tapes describe the intended finite
leaf independently from a concrete transition table.  The source tape starts at
the left boundary of the mixed parser-stack/source-rest segment, while the
target tape has already emitted the header and quoted prefix and leaves
{lit}`stageBits ++ sourceRestBits` as the live right-hand tail.
-/

def MixedParserStackRewriterSourceTape
    (prefixCells : List (Option Bool))
    (stageBits sourceRestBits quoteRestBits : Word Bool) : Tape Bool :=
  scanLeftToBlankLeftHaltTape
    (List.append
      (sourceRestBits.reverse.map some)
      (List.append (stageBits.reverse.map some)
        prefixCells.reverse))
    quoteRestBits
    [none]

def MixedParserStackRewriterTargetTape
    (prefixQuote lengthHeader : Word Bool)
    (stageBits sourceRestBits quoteRestBits : Word Bool) : Tape Bool :=
  tapeAtCells
    ((List.append lengthHeader
      (List.append prefixQuote quoteRestBits)).reverse.map some)
    ((List.append stageBits sourceRestBits).map some)

theorem mixedParserStack_defaultBits_length
    (cells : List (Option Bool)) :
    (cells.map optionBitDefaultFalse).length = cells.length := by
  simp

def mixedParserStackQuotedCellBits (cell : Option Bool) : Word Bool :=
  match cell with
  | none => preservingCellPassZeroBits
  | some false => preservingCellPassZeroBits
  | some true => preservingCellPassOneBits

def mixedParserStackQuotedCellsBits :
    List (Option Bool) -> Word Bool
  | [] => []
  | cell :: rest =>
      List.append
        (mixedParserStackQuotedCellBits cell)
        (mixedParserStackQuotedCellsBits rest)

theorem mixedParserStackQuotedCellsBits_append
    (pref suffix : List (Option Bool)) :
    mixedParserStackQuotedCellsBits (List.append pref suffix) =
      List.append (mixedParserStackQuotedCellsBits pref)
        (mixedParserStackQuotedCellsBits suffix) := by
  induction pref with
  | nil =>
      rfl
  | cons cell rest ih =>
      change
        mixedParserStackQuotedCellsBits
            (cell :: List.append rest suffix) =
          List.append
            (List.append (mixedParserStackQuotedCellBits cell)
              (mixedParserStackQuotedCellsBits rest))
            (mixedParserStackQuotedCellsBits suffix)
      change
        List.append (mixedParserStackQuotedCellBits cell)
            (mixedParserStackQuotedCellsBits
              (List.append rest suffix)) =
          List.append
            (List.append (mixedParserStackQuotedCellBits cell)
              (mixedParserStackQuotedCellsBits rest))
            (mixedParserStackQuotedCellsBits suffix)
      rw [ih]
      exact
        (List.append_assoc
          (mixedParserStackQuotedCellBits cell)
          (mixedParserStackQuotedCellsBits rest)
          (mixedParserStackQuotedCellsBits suffix)).symm

theorem mixedParserStackQuotedCellsBits_eq_defaultBits
    (cells : List (Option Bool)) :
    mixedParserStackQuotedCellsBits cells =
      preservingCellPassCellBits
        (List.map optionBitDefaultFalse cells) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      cases cell with
      | none =>
          simp [mixedParserStackQuotedCellsBits,
            mixedParserStackQuotedCellBits, optionBitDefaultFalse,
            preservingCellPassCellBits, preservingCellPassZeroBits,
            ih]
      | some b =>
          cases b <;>
            simp [mixedParserStackQuotedCellsBits,
              mixedParserStackQuotedCellBits, optionBitDefaultFalse,
              preservingCellPassCellBits, preservingCellPassZeroBits,
              preservingCellPassOneBits, ih]

theorem mixedParserStackQuotedCellsBits_length
    (cells : List (Option Bool)) :
    (mixedParserStackQuotedCellsBits cells).length =
      4 * cells.length := by
  rw [mixedParserStackQuotedCellsBits_eq_defaultBits]
  rw [preservingCellPassCellBits_length]
  simp

theorem mixedParserStackQuotedCellsBits_cons_none
    (cells : List (Option Bool)) :
    mixedParserStackQuotedCellsBits (none :: cells) =
      List.append preservingCellPassZeroBits
        (mixedParserStackQuotedCellsBits cells) := by
  rfl

theorem mixedParserStackQuotedCellsBits_marker_split
    (w : Word Bool) :
    mixedParserStackQuotedCellsBits
        (assemblySourceRestFinishParserPrefixCells w) =
      List.append
        (mixedParserStackQuotedCellsBits
          assemblySourceRestFinishParserMarkerLeftCells)
        (List.append preservingCellPassZeroBits
          (mixedParserStackQuotedCellsBits
            (assemblySourceRestFinishParserMarkerRightCells w))) := by
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split,
    mixedParserStackQuotedCellsBits_append]
  rfl

theorem assemblySourceRestFinishParserPrefixCells_defaultBits_marker_split
    (w : Word Bool) :
    List.map optionBitDefaultFalse
        (assemblySourceRestFinishParserPrefixCells w) =
      List.append
        (List.map optionBitDefaultFalse
          assemblySourceRestFinishParserMarkerLeftCells)
        (false ::
          assemblySourceRestFinishParserMarkerRightBits w) := by
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  rw [assemblySourceRestFinishParserMarkerRightCells_eq_bits]
  simp [List.map_append, List.map_map, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some]

theorem mixedParserStackQuotedCellsBits_markerRight_eq_bits
    (w : Word Bool) :
    mixedParserStackQuotedCellsBits
        (assemblySourceRestFinishParserMarkerRightCells w) =
      preservingCellPassCellBits
        (assemblySourceRestFinishParserMarkerRightBits w) := by
  rw [mixedParserStackQuotedCellsBits_eq_defaultBits,
    assemblySourceRestFinishParserMarkerRightCells_eq_bits]
  simp [List.map_map, optionBitDefaultFalse_map_some]

def MixedParserStackRewriterPrefixQuote
    (prefixCells : List (Option Bool)) (stageBits : Word Bool) :
    Word Bool :=
  List.append
    (mixedParserStackQuotedCellsBits prefixCells)
    (preservingCellPassCellBits stageBits)

def MixedParserStackRewriterLengthHeader
    (prefixCells : List (Option Bool))
    (stageBits sourceRestBits : Word Bool) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.header)
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      (prefixCells.length + stageBits.length + sourceRestBits.length))

theorem MixedParserStackRewriterPrefixQuote_marker_split
    (w : Word Bool) (stageBits : Word Bool) :
    MixedParserStackRewriterPrefixQuote
        (assemblySourceRestFinishParserPrefixCells w)
        stageBits =
      List.append
        (mixedParserStackQuotedCellsBits
          assemblySourceRestFinishParserMarkerLeftCells)
        (List.append preservingCellPassZeroBits
          (List.append
            (mixedParserStackQuotedCellsBits
              (assemblySourceRestFinishParserMarkerRightCells w))
            (preservingCellPassCellBits stageBits))) := by
  rw [MixedParserStackRewriterPrefixQuote,
    mixedParserStackQuotedCellsBits_marker_split]
  simp [List.append_assoc]

theorem assemblySourceRestFinishSourcePrefixBits_length_eq_fields
    (w : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishSourcePrefixBits w stage).length =
      4 + (DovetailInitialLayoutInitializer.stageInputBits w stage).length := by
  rw [assemblySourceRestFinishSourcePrefixBits_eq_fields]
  simp [encodeCodeSymbolAsInput]
  omega

theorem assemblySourceRestFinishSourceBits_length_eq_prefix_add
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishSourceBits w sourceRestBits stage).length =
      (assemblySourceRestFinishSourcePrefixBits w stage).length +
        sourceRestBits.length := by
  rw [assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  simp

theorem assemblySourceRestFinishSourceBits_headerPrefix
    (w sourceRestBits : Word Bool) (stage : Nat) :
    exists rest : Word Bool,
      assemblySourceRestFinishSourceBits w sourceRestBits stage =
        false :: false :: false :: true :: rest := by
  refine
    ⟨List.append
      (DovetailInitialLayoutInitializer.stageInputBits w stage)
      sourceRestBits, ?_⟩
  simp [assemblySourceRestFinishSourceBits, encodeCodeSymbolAsInput]

theorem assemblySourceRestFinishSourceBits_length_ge_header
    (w sourceRestBits : Word Bool) (stage : Nat) :
    4 <= (assemblySourceRestFinishSourceBits w sourceRestBits stage).length := by
  rw [assemblySourceRestFinishSourceBits_eq]
  simp [encodeCodeSymbolAsInput]

theorem assemblySourceRestFinishTargetPrefixBits_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
          (preservingCellPassCellBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage))) := by
  rfl

theorem assemblySourceRestFinishTargetPrefixBits_eq_encodeBoolWordAppend
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend
            (assemblySourceRestFinishSourceBits w sourceRestBits stage)
            []) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote]
  exact
    preservingCellPassHeaderQuoteBits_eq_encodeBoolWordAppend
      (assemblySourceRestFinishSourceBits w sourceRestBits stage)

theorem preservingCellPassCellBits_append_bool
    (pref suffix : Word Bool) :
    preservingCellPassCellBits (List.append pref suffix) =
      List.append (preservingCellPassCellBits pref)
        (preservingCellPassCellBits suffix) := by
  induction pref with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b
      · simp [preservingCellPassCellBits, preservingCellPassZeroBits]
        change
          false :: true :: false :: true ::
              preservingCellPassCellBits (List.append rest suffix) =
            false :: true :: false :: true ::
              List.append (preservingCellPassCellBits rest)
                (preservingCellPassCellBits suffix)
        rw [ih]
      · simp [preservingCellPassCellBits, preservingCellPassOneBits]
        change
          false :: true :: true :: false ::
              preservingCellPassCellBits (List.append rest suffix) =
            false :: true :: true :: false ::
              List.append (preservingCellPassCellBits rest)
                (preservingCellPassCellBits suffix)
        rw [ih]

theorem assemblySourceRestFinishSourcePrefixBits_eq_split_defaulted
    (w : Word Bool) (stage : Nat)
    (prefixCells : List (Option Bool))
    (hsplit :
      assemblySourceRestFinishParserStackCells w stage =
        List.append prefixCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)) :
    assemblySourceRestFinishSourcePrefixBits w stage =
      List.append (List.map optionBitDefaultFalse prefixCells)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage) := by
  rw [← assemblySourceRestFinishParserStackCells_defaultBits w stage]
  rw [hsplit]
  simp [List.map_append, List.map_map, optionBitDefaultFalse_map_some]

theorem MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix_of_split
    (w : Word Bool) (stage : Nat)
    (prefixCells : List (Option Bool))
    (hsplit :
      assemblySourceRestFinishParserStackCells w stage =
        List.append prefixCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)) :
    MixedParserStackRewriterPrefixQuote prefixCells
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage) =
      assemblySourceRestFinishQuotedPrefixBits w stage := by
  rw [MixedParserStackRewriterPrefixQuote,
    assemblySourceRestFinishQuotedPrefixBits,
    assemblySourceRestFinishSourcePrefixBits_eq_split_defaulted
      w stage prefixCells hsplit,
    preservingCellPassCellBits_append_bool,
    mixedParserStackQuotedCellsBits_eq_defaultBits]

theorem MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader_of_split
    (w sourceRestBits : Word Bool) (stage : Nat)
    (prefixCells : List (Option Bool))
    (hsplit :
      assemblySourceRestFinishParserStackCells w stage =
        List.append prefixCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)) :
    MixedParserStackRewriterLengthHeader prefixCells
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits =
      assemblySourceRestFinishLengthHeaderBits
        w sourceRestBits stage := by
  have hprefix :=
    assemblySourceRestFinishSourcePrefixBits_eq_split_defaulted
      w stage prefixCells hsplit
  have hlen :
      (assemblySourceRestFinishSourcePrefixBits w stage).length =
        prefixCells.length +
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).length := by
    rw [hprefix]
    simp
  simp [MixedParserStackRewriterLengthHeader,
    assemblySourceRestFinishLengthHeaderBits, hlen, Nat.add_assoc]

theorem MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix
    (w : Word Bool) (stage : Nat) :
    MixedParserStackRewriterPrefixQuote
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage) =
      assemblySourceRestFinishQuotedPrefixBits w stage :=
  MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix_of_split
    w stage (assemblySourceRestFinishParserPrefixCells w)
    (assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat
      w stage)

theorem MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterLengthHeader
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits =
      assemblySourceRestFinishLengthHeaderBits
        w sourceRestBits stage :=
  MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader_of_split
    w sourceRestBits stage
    (assemblySourceRestFinishParserPrefixCells w)
    (assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat
      w stage)

theorem assemblySourceRestFinishTargetPrefixBits_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourcePrefixBits w stage))
            (preservingCellPassCellBits sourceRestBits))) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest,
    preservingCellPassCellBits_append_bool]

theorem assemblySourceRestFinishTargetPrefixBits_eq_splitQuote_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourcePrefixBits w stage))
            (preservingCellPassCellBits sourceRestBits))) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote,
    assemblySourceRestFinishSourceBits_length_eq_prefix_add]

theorem assemblySourceRestFinishTargetPrefixBits_eq_named_splitQuote_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (assemblySourceRestFinishQuotedPrefixBits w stage)
            (preservingCellPassCellBits sourceRestBits))) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote_prefixLength]
  rfl

theorem assemblySourceRestFinishTargetPrefixBits_eq_named_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (assemblySourceRestFinishQuotedPrefixBits w stage)
            (preservingCellPassCellBits sourceRestBits))) :=
  assemblySourceRestFinishTargetPrefixBits_eq_named_splitQuote_prefixLength
    w sourceRestBits stage

theorem assemblySourceRestFinishTargetPrefixBits_eq_lengthHeader_append_quoteRest
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishLengthHeaderBits
          w sourceRestBits stage)
        (List.append
          (assemblySourceRestFinishQuotedPrefixBits w stage)
          (preservingCellPassCellBits sourceRestBits)) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_named_fields_prefixLength,
    assemblySourceRestFinishLengthHeaderBits]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetPrefixBits_eq_prefixQuote_append_restQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_lengthHeader_append_quoteRest,
    assemblySourceRestFinishPrefixQuoteOutputBits]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetPrefixBits_length_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage).length =
      4 +
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (assemblySourceRestFinishSourceBits w sourceRestBits stage).length).length +
        4 * (assemblySourceRestFinishSourceBits w sourceRestBits stage).length := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote]
  simp [encodeCodeSymbolAsInput, preservingCellPassCellBits_length]
  omega

theorem assemblySourceRestFinishTargetPrefixBits_length_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage).length =
      4 +
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (assemblySourceRestFinishSourceBits w sourceRestBits stage).length).length +
        4 * (assemblySourceRestFinishSourcePrefixBits w stage).length +
        4 * sourceRestBits.length := by
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote]
  simp [encodeCodeSymbolAsInput, preservingCellPassCellBits_length,
    Nat.add_assoc]
  omega

/-!
**Exact source, boundary, and target tapes.**  These definitions pin down the
physical tape windows used by the finish phase.  The accompanying facts give
both {name}`Tape.cells` and {name}`Tape.normalizedOutput` views so later
subroutine composition can use exact-tape handoffs rather than semantic output
shortcuts.
-/

def assemblySourceRestFinishSourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    (none :: List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (List.append
      ((preservingCellPassCellBits sourceRestBits).map some)
      [none])

def assemblySourceRestFinishPostBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells (assemblySourceRestBoundaryLeftRev w stage)
    (List.append (sourceRestBits.map some) [none])

def assemblySourceRestFinishBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (none ::
      List.append
        ((preservingCellPassCellBits sourceRestBits).map some)
        [none])

def assemblySourceRestFinishTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((assemblySourceRestFinishTargetPrefixBits
      w sourceRestBits stage).reverse.map some)
    ((List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage)
      sourceRestBits).map some)

theorem assemblySourceRestFinishSourceTape_cells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rw [assemblySourceRestFinishSourceTape]
  cases preservingCellPassCellBits sourceRestBits <;>
    simp [tapeAtCells, Tape.cells,
      List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishBoundaryTape_cells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rw [assemblySourceRestFinishBoundaryTape]
  cases preservingCellPassCellBits sourceRestBits <;>
    simp [tapeAtCells, Tape.cells,
      List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishTargetTape_cells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [assemblySourceRestFinishTargetTape, hstage]
  simp [tapeAtCells, Tape.cells,
    List.map_reverse, List.map_append]

theorem assemblySourceRestFinishSourceTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) :=
  assemblySourceRestFinishSourceTape_cells_eq_fields w sourceRestBits stage

theorem assemblySourceRestFinishSourceTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishSourceTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishSourceTape_cells]
  have hprefix :=
    assemblySourceRestBoundaryLeftRev_defaultBits_append
      w sourceRestBits stage
  simpa [assemblySourceRestFinishSourceBits, optionBitDefaultFalse,
    Function.comp_def, List.map_append,
    List.map_reverse, List.append_assoc] using
    congrArg
      (fun pref =>
        List.append pref
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false]))
      hprefix

theorem assemblySourceRestFinishSourceTape_defaultedCells_eq_named_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishSourceTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishRawSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishSourceTape_defaultedCells,
    assemblySourceRestFinishRawSourceBits]

theorem assemblySourceRestFinishBoundaryTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) :=
  assemblySourceRestFinishBoundaryTape_cells_eq_fields w sourceRestBits stage

theorem assemblySourceRestFinishBoundaryTape_cells_eq_sourceTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) =
      Tape.cells
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishBoundaryTape_cells,
    assemblySourceRestFinishSourceTape_cells]

theorem assemblySourceRestFinishBoundaryTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishBoundaryTape_cells_eq_sourceTape_cells]
  exact assemblySourceRestFinishSourceTape_defaultedCells
    w sourceRestBits stage

theorem assemblySourceRestFinishBoundaryTape_defaultedCells_eq_named_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishRawSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishBoundaryTape_defaultedCells,
    assemblySourceRestFinishRawSourceBits]

theorem assemblySourceRestFinishBoundaryTape_defaultedCells_eq_prefix_sourceRest_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        (List.append sourceRestBits
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rw [assemblySourceRestFinishBoundaryTape_defaultedCells,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) :=
  assemblySourceRestFinishTargetTape_cells_eq_fields w sourceRestBits stage

theorem assemblySourceRestFinishTargetTape_cells_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourceBits
                w sourceRestBits stage)))).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_headerQuote]

theorem assemblySourceRestFinishTargetTape_cells_eq_encodeBoolWordAppend
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend
              (assemblySourceRestFinishSourceBits w sourceRestBits stage)
              [])).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_encodeBoolWordAppend]

theorem assemblySourceRestFinishTargetTape_cells_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits)))).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote]

theorem assemblySourceRestFinishTargetTape_cells_eq_splitQuote_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              ((assemblySourceRestFinishSourcePrefixBits w stage).length +
                sourceRestBits.length))
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits)))).map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_splitQuote,
    assemblySourceRestFinishSourceBits_length_eq_prefix_add]

theorem assemblySourceRestFinishTargetTape_cells_eq_named_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              ((assemblySourceRestFinishSourcePrefixBits w stage).length +
                sourceRestBits.length))
            (List.append
              (assemblySourceRestFinishQuotedPrefixBits w stage)
              (preservingCellPassCellBits sourceRestBits)))).map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_splitQuote_prefixLength,
    assemblySourceRestFinishQuotedPrefixBits,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_cells_eq_targetBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      (assemblySourceRestFinishTargetBits
        w sourceRestBits stage).map some := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_named_fields_prefixLength,
    assemblySourceRestFinishTargetBits,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishLengthHeaderBits]
  simp [List.map_append, List.append_assoc]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_splitQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits))))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_splitQuote]
  simp [optionBitDefaultFalse, Function.comp_def, List.map_append,
    List.append_assoc]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourcePrefixBits w stage))
            (List.append
              (preservingCellPassCellBits sourceRestBits)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                sourceRestBits)))) := by
  rw [assemblySourceRestFinishTargetTape_defaultedCells_eq_splitQuote]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourcePrefixBits w stage))
            (List.append
              (preservingCellPassCellBits sourceRestBits)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                sourceRestBits)))) := by
  rw [assemblySourceRestFinishTargetTape_defaultedCells_eq_fields,
    assemblySourceRestFinishSourceBits_length_eq_prefix_add]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_named_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (assemblySourceRestFinishQuotedPrefixBits w stage)
            (List.append
              (preservingCellPassCellBits sourceRestBits)
              (assemblySourceRestFinishRawTailBits
                sourceRestBits stage)))) := by
  rw [assemblySourceRestFinishTargetTape_defaultedCells_eq_fields_prefixLength,
    assemblySourceRestFinishQuotedPrefixBits,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_targetBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      assemblySourceRestFinishTargetBits w sourceRestBits stage := by
  rw [assemblySourceRestFinishTargetTape_defaultedCells_eq_named_fields_prefixLength,
    assemblySourceRestFinishTargetBits,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishLengthHeaderBits]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetTape_defaultedCells_eq_headerQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage).length)
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourceBits w sourceRestBits stage))))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_headerQuote]
  simp [optionBitDefaultFalse, Function.comp_def, List.map_append,
    List.append_assoc]

theorem
    assemblySourceRestFinishTargetTape_defaultedCells_eq_encodeBoolWordAppend
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishTargetTape w sourceRestBits stage)) =
      List.append
        (encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend
              (assemblySourceRestFinishSourceBits w sourceRestBits stage)
              []))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_cells_eq_encodeBoolWordAppend]
  simp [optionBitDefaultFalse, Function.comp_def, List.map_append]

theorem assemblySourceRestFinishTargetTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        (assemblySourceRestFinishTargetPrefixBits w sourceRestBits stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [Tape.normalizedOutput]
  rw [assemblySourceRestFinishTargetTape_cells]
  simp [Function.comp_def, List.map_append]

theorem assemblySourceRestFinishTargetTape_normalizedOutput_eq_encodeBoolWordAppend
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        (encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend
              (assemblySourceRestFinishSourceBits w sourceRestBits stage)
              []))
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_encodeBoolWordAppend]

theorem assemblySourceRestFinishTargetTape_normalizedOutput_eq_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourcePrefixBits w stage))
            (List.append
              (preservingCellPassCellBits sourceRestBits)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage)
                sourceRestBits)))) := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput]
  rw [assemblySourceRestFinishTargetPrefixBits_eq_splitQuote_prefixLength]
  simp [List.append_assoc]

theorem assemblySourceRestFinishTargetTape_normalizedOutput_eq_named_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            ((assemblySourceRestFinishSourcePrefixBits w stage).length +
              sourceRestBits.length))
          (List.append
            (assemblySourceRestFinishQuotedPrefixBits w stage)
            (List.append
              (preservingCellPassCellBits sourceRestBits)
              (assemblySourceRestFinishRawTailBits
                sourceRestBits stage)))) := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput_eq_fields_prefixLength,
    assemblySourceRestFinishQuotedPrefixBits,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_normalizedOutput_eq_targetBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) =
      assemblySourceRestFinishTargetBits w sourceRestBits stage := by
  rw [assemblySourceRestFinishTargetTape_normalizedOutput_eq_named_fields_prefixLength,
    assemblySourceRestFinishTargetBits,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishLengthHeaderBits]
  simp [List.append_assoc]

/-!
**Construction contracts.**  The public finish specification starts at
{name}`assemblySourceRestFinishSourceTape`.  The intermediate contracts expose
the exact scanner handoff points: the post-boundary tape, the quote-boundary
tape, and the left-boundary tape used by the still-local core copier.
-/

def AssemblySourceRestFinishSpec (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishSourceTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishSpec finish

def AssemblySourceRestFinishBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishBoundarySpec finish

def assemblySourceRestFinishLeftMoveDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1 ]

theorem assemblySourceRestFinishLeftMoveDescription_wellFormed :
    assemblySourceRestFinishLeftMoveDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := assemblySourceRestFinishLeftMoveDescription.transitions)
      (stateCount := assemblySourceRestFinishLeftMoveDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := assemblySourceRestFinishLeftMoveDescription.transitions)
      (by decide)

theorem assemblySourceRestFinishLeftMoveDescription_haltTransitionFree :
    assemblySourceRestFinishLeftMoveDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := assemblySourceRestFinishLeftMoveDescription.transitions)
    (state := assemblySourceRestFinishLeftMoveDescription.halt)
    (by decide)

theorem assemblySourceRestFinishLeftMoveDescription_subroutineReady :
    assemblySourceRestFinishLeftMoveDescription.SubroutineReady :=
  ⟨assemblySourceRestFinishLeftMoveDescription_wellFormed,
    assemblySourceRestFinishLeftMoveDescription_haltTransitionFree⟩

theorem assemblySourceRestFinishLeftMoveDescription_haltsFromTape
    (T : Tape Bool) :
    assemblySourceRestFinishLeftMoveDescription.HaltsFromTape T
      (Tape.move Direction.left T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [assemblySourceRestFinishLeftMoveDescription,
              runConfig, stepConfig, lookupTransition, Matches,
              transition, Tape.read, Tape.write, Tape.move]
        | some b =>
            cases b <;>
              simp [assemblySourceRestFinishLeftMoveDescription,
                runConfig, stepConfig, lookupTransition, Matches,
                transition, Tape.read, Tape.write, Tape.move]

theorem tapeAtCells_move_left_cons_append_singleton
    (left cells : List (Option Bool)) :
    Tape.move Direction.left
        (tapeAtCells (none :: left) (List.append cells [none])) =
      tapeAtCells left (none :: List.append cells [none]) := by
  cases cells <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft]

theorem tapeAtCells_move_left_move_right_none_cons_append_singleton
    (left cells : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells left (none :: List.append cells [none]))) =
      tapeAtCells left (none :: List.append cells [none]) := by
  cases cells <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tapeAtCells_move_left_none_cons_cells_of_left_ne_nil
    (left right : List (Option Bool)) (hleft : left ≠ []) :
    Tape.cells (Tape.move Direction.left (tapeAtCells left (none :: right))) =
      List.append left.reverse (none :: right) := by
  cases left with
  | nil =>
      contradiction
  | cons cell rest =>
      simp [tapeAtCells, Tape.cells, Tape.move, Tape.moveLeft]

theorem MixedParserStackRewriterSourceTape_cells_of_left_ne_nil
    (prefixCells : List (Option Bool))
    (stageBits sourceRestBits quoteRestBits : Word Bool)
    (hleft :
      List.append
        (sourceRestBits.reverse.map some)
        (List.append (stageBits.reverse.map some)
          prefixCells.reverse) ≠ []) :
    Tape.cells
        (MixedParserStackRewriterSourceTape
          prefixCells stageBits sourceRestBits quoteRestBits) =
      List.append prefixCells
        (List.append (stageBits.map some)
          (List.append (sourceRestBits.map some)
            (none ::
              List.append (quoteRestBits.map some) [none]))) := by
  rw [MixedParserStackRewriterSourceTape,
    scanLeftToBlankLeftHaltTape]
  rw [tapeAtCells_move_left_none_cons_cells_of_left_ne_nil _ _ hleft]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem MixedParserStackRewriterSourceTape_cells_stageNat
    (prefixCells : List (Option Bool))
    (sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterSourceTape prefixCells
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits quoteRestBits) =
      List.append prefixCells
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (List.append (sourceRestBits.map some)
            (none ::
              List.append (quoteRestBits.map some) [none]))) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  exact
    MixedParserStackRewriterSourceTape_cells_of_left_ne_nil
      prefixCells
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage)
      sourceRestBits quoteRestBits
      (by
        cases sourceRestBits with
        | nil =>
            simp [hstage]
        | cons bit rest =>
            simp)

theorem MixedParserStackRewriterSourceTape_cells_marker_split_stageNat
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterSourceTape
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits quoteRestBits) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            (assemblySourceRestFinishParserMarkerRightCells w)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append (quoteRestBits.map some) [none])))) := by
  rw [MixedParserStackRewriterSourceTape_cells_stageNat]
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  simp [List.append_assoc]

theorem assemblySourceRestFinishSourceTape_move_left
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) =
      assemblySourceRestFinishBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishSourceTape,
    assemblySourceRestFinishBoundaryTape]
  exact
    tapeAtCells_move_left_cons_append_singleton
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      ((preservingCellPassCellBits sourceRestBits).map some)

theorem assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishLeftMoveDescription.HaltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) := by
  simpa [assemblySourceRestFinishSourceTape_move_left] using
    assemblySourceRestFinishLeftMoveDescription_haltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)

theorem assemblySourceRestFinishBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      assemblySourceRestFinishBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishBoundaryTape]
  exact
    tapeAtCells_move_left_move_right_none_cons_append_singleton
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      ((preservingCellPassCellBits sourceRestBits).map some)

/-!
**Scanner handoff reductions.**  The first reductions move from the source tape
to the quote boundary by scanning across the already-quoted source-rest field,
then back to the left boundary.  They are stated as exact
{name}`MachineDescription.HaltsFromTape` facts so the final construction can be
assembled with {name}`SeqViaCanonical`.
-/

def assemblySourceRestFinishQuoteBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanRightToBlankLeftHaltTape
    (none :: List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (preservingCellPassCellBits sourceRestBits)

def AssemblySourceRestFinishQuoteBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishQuoteBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishQuoteBoundarySpec finish

theorem scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishSourceTape,
    assemblySourceRestFinishQuoteBoundaryTape]
  exact
    scanRightToBlankLeftDescription_haltsFromTape
      (none :: List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)

theorem assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishQuoteBoundaryTape
            w sourceRestBits stage)) =
      assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage := by
  cases hquote : preservingCellPassCellBits sourceRestBits with
  | nil =>
      rw [assemblySourceRestFinishQuoteBoundaryTape, hquote]
      simp [scanRightToBlankLeftHaltTape, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons quoteHead quoteTail =>
      rw [assemblySourceRestFinishQuoteBoundaryTape, hquote]
      exact
        scanRightToBlankLeftHaltTape_move_left_move_right_cons
          (none :: List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
          quoteHead quoteTail

def assemblySourceRestFinishLeftBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanLeftToBlankLeftHaltTape
    (List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (preservingCellPassCellBits sourceRestBits)
    [none]

def AssemblySourceRestFinishLeftBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishLeftBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishLeftBoundarySpec finish

def AssemblySourceRestFinishLeftBoundaryCoreSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishLeftBoundaryCoreConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishLeftBoundaryCoreSpec finish

theorem assemblySourceRestFinishLeftBoundaryConstruction_of_core
    (h : AssemblySourceRestFinishLeftBoundaryCoreConstruction) :
    AssemblySourceRestFinishLeftBoundaryConstruction := by
  exact h

theorem scanLeftToBlankLeftHaltTape_cons
    (cell : Option Bool) (leftBase : List (Option Bool))
    (bits : Word Bool) (right : List (Option Bool)) :
    scanLeftToBlankLeftHaltTape (cell :: leftBase) bits right =
      { left := leftBase
        head := cell
        right := none :: List.append (bits.map some) right } := by
  simp [scanLeftToBlankLeftHaltTape, tapeAtCells, Tape.move,
    Tape.moveLeft]

theorem scanLeftToBlankLeftHaltTape_right_of_left_ne_nil
    (leftBase : List (Option Bool)) (bits : Word Bool)
    (right : List (Option Bool)) (hleft : leftBase ≠ []) :
    (scanLeftToBlankLeftHaltTape leftBase bits right).right =
      none :: List.append (bits.map some) right := by
  cases leftBase with
  | nil =>
      contradiction
  | cons cell rest =>
      simp [scanLeftToBlankLeftHaltTape_cons]

theorem assemblySourceRestBoundaryLeftRev_ne_nil
    (w : Word Bool) (stage : Nat) :
    assemblySourceRestBoundaryLeftRev w stage ≠ [] := by
  cases w <;>
    simp [assemblySourceRestBoundaryLeftRev]

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rw [assemblySourceRestFinishLeftBoundaryTape,
    scanLeftToBlankLeftHaltTape]
  have hleft :
      List.append (sourceRestBits.reverse.map some)
          (assemblySourceRestBoundaryLeftRev w stage) ≠ [] := by
    cases sourceRestBits with
    | nil =>
        simpa using assemblySourceRestBoundaryLeftRev_ne_nil w stage
    | cons bit rest =>
        simp
  rw [tapeAtCells_move_left_none_cons_cells_of_left_ne_nil _ _ hleft]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_prefix_sourceRest_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) :=
  assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields
    w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_marker_split
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            (assemblySourceRestFinishParserMarkerRightCells w)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none])))) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields]
  change
    List.append
      (assemblySourceRestFinishParserStackCells w stage)
      (List.append
        (sourceRestBits.map some)
        (none ::
          List.append
            ((preservingCellPassCellBits sourceRestBits).map some)
            [none])) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            (assemblySourceRestFinishParserMarkerRightCells w)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none]))))
  rw [assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat]
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  simp [List.append_assoc]

theorem assemblySourceRestFinishLeftBoundaryTape_cells_nil_eq_marker_split
    (sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape
          ([] : Word Bool) sourceRestBits stage) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            ([true, true].map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none])))) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_marker_split]
  rfl

theorem assemblySourceRestFinishLeftBoundaryTape_cells_cons_eq_marker_split
    (b : Bool) (rest sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape
          (b :: rest) sourceRestBits stage) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            ((true :: false ::
              List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  rest.length)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                    b)
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest))).map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none])))) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_marker_split]
  rfl

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_boundaryTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields,
    assemblySourceRestFinishBoundaryTape_cells]

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_boundaryTape_cells]
  exact assemblySourceRestFinishBoundaryTape_defaultedCells
    w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_sourceBits_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) :=
  assemblySourceRestFinishLeftBoundaryTape_defaultedCells
    w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_named_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishRawSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_defaultedCells,
    assemblySourceRestFinishRawSourceBits]

theorem
    assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_prefix_sourceRest_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        (List.append sourceRestBits
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_defaultedCells,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  simp [List.append_assoc]

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        (List.append sourceRestBits
          (List.append [false]
            (List.append (preservingCellPassCellBits sourceRestBits)
              [false]))) := by
  rw [
    assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_prefix_sourceRest_quote]
  simp

theorem assemblySourceRestFinishLeftBoundaryTape_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage).right =
      none ::
        List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none] := by
  rw [assemblySourceRestFinishLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_right_of_left_ne_nil
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)
      [none]
      (by
        cases sourceRestBits with
        | nil =>
            simpa using assemblySourceRestBoundaryLeftRev_ne_nil w stage
        | cons bit rest =>
            simp)

theorem MixedParserStackRewriterSourceTape_eq_leftBoundary_of_split
    (w sourceRestBits : Word Bool) (stage : Nat)
    (prefixCells : List (Option Bool))
    (hsplit :
      assemblySourceRestFinishParserStackCells w stage =
        List.append prefixCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)) :
    MixedParserStackRewriterSourceTape prefixCells
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishLeftBoundaryTape
        w sourceRestBits stage := by
  have hboundary :
      assemblySourceRestBoundaryLeftRev w stage =
        List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          prefixCells.reverse := by
    have hrev := congrArg List.reverse hsplit
    simpa [assemblySourceRestFinishParserStackCells,
      List.reverse_append, List.map_reverse] using hrev
  rw [MixedParserStackRewriterSourceTape,
    assemblySourceRestFinishLeftBoundaryTape, hboundary]

theorem
    exists_MixedParserStackRewriterSourceTape_eq_leftBoundary
    (w sourceRestBits : Word Bool) (stage : Nat) :
    exists prefixCells : List (Option Bool),
      MixedParserStackRewriterSourceTape prefixCells
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits) =
        assemblySourceRestFinishLeftBoundaryTape
          w sourceRestBits stage := by
  rcases
      assemblySourceRestFinishParserStackCells_eq_prefix_append_stageNat
        w stage with
    ⟨prefixCells, hsplit⟩
  exact
    ⟨prefixCells,
      MixedParserStackRewriterSourceTape_eq_leftBoundary_of_split
        w sourceRestBits stage prefixCells hsplit⟩

theorem MixedParserStackRewriterSourceTape_eq_leftBoundary
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterSourceTape
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishLeftBoundaryTape
        w sourceRestBits stage :=
  MixedParserStackRewriterSourceTape_eq_leftBoundary_of_split
    w sourceRestBits stage
    (assemblySourceRestFinishParserPrefixCells w)
    (assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat
      w stage)

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              ((assemblySourceRestFinishSourcePrefixBits w stage).length +
                sourceRestBits.length))
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits)))).reverse.map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishTargetPrefixBits_eq_splitQuote_prefixLength]

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_named_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_named_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              ((assemblySourceRestFinishSourcePrefixBits w stage).length +
                sourceRestBits.length))
            (List.append
              (assemblySourceRestFinishQuotedPrefixBits w stage)
              (preservingCellPassCellBits sourceRestBits)))).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishTargetPrefixBits_eq_named_fields_prefixLength,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_segments
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((List.append
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishTargetPrefixBits_eq_prefixQuote_append_restQuote,
    assemblySourceRestFinishRawTailBits]

theorem MixedParserStackRewriterTargetTape_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterTargetTape
        (assemblySourceRestFinishQuotedPrefixBits w stage)
        (assemblySourceRestFinishLengthHeaderBits
          w sourceRestBits stage)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [MixedParserStackRewriterTargetTape,
    assemblySourceRestFinishTargetTape_eq_tapeAtCells_segments,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishRawTailBits]
  simp [List.append_assoc]

def assemblySourceRestFinishLengthHeaderTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((assemblySourceRestFinishLengthHeaderBits
      w sourceRestBits stage).reverse.map some)
    ((List.append
      (assemblySourceRestFinishQuotedPrefixBits w stage)
      (List.append
        (preservingCellPassCellBits sourceRestBits)
        (assemblySourceRestFinishRawTailBits
          sourceRestBits stage))).map some)

def assemblySourceRestFinishPrefixQuotedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((assemblySourceRestFinishPrefixQuoteOutputBits
      w sourceRestBits stage).reverse.map some)
    ((List.append
      (preservingCellPassCellBits sourceRestBits)
      (assemblySourceRestFinishRawTailBits
        sourceRestBits stage)).map some)

def assemblySourceRestFinishQuoteRestJoinedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((List.append
      (assemblySourceRestFinishPrefixQuoteOutputBits
        w sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits)).reverse.map some)
    ((assemblySourceRestFinishRawTailBits
      sourceRestBits stage).map some)

def assemblySourceRestFinishTailCopiedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  assemblySourceRestFinishQuoteRestJoinedTape w sourceRestBits stage

theorem assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishQuoteRestJoinedTape w sourceRestBits stage =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishQuoteRestJoinedTape,
    assemblySourceRestFinishTargetTape_eq_tapeAtCells_segments]

theorem assemblySourceRestFinishTailCopiedTape_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTailCopiedTape w sourceRestBits stage =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishTailCopiedTape,
    assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape]

/-!
**Phase composition.**  The remaining lemmas compose the small scanners around
the left-boundary core.  The only finite-machine leaf still hidden behind the
core construction is the copier that consumes the mixed parser-stack layout and
emits the normalized target tape.
-/

theorem preservingCellPassHaltTape_eq_assemblySourceRestFinishSourceTape
    (w : Word Bool) (b : Bool) (rest : Word Bool) (stage : Nat) :
    preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev w stage) (b :: rest) [] =
      assemblySourceRestFinishSourceTape w (b :: rest) stage := by
  simpa [assemblySourceRestFinishSourceTape] using
    preservingCellPassHaltTape_nonempty_empty_output_eq_tapeAtCells
      (assemblySourceRestBoundaryLeftRev w stage) b rest

theorem preservingCellPassDescription_haltsFrom_finishPostBoundaryTape
    (w : Word Bool) (b : Bool) (rest : Word Bool) (stage : Nat) :
    PreservingCellPassDescription.HaltsFromTape
      (assemblySourceRestFinishPostBoundaryTape w (b :: rest) stage)
      (assemblySourceRestFinishSourceTape w (b :: rest) stage) := by
  rw [assemblySourceRestFinishPostBoundaryTape]
  rw [← preservingCellPassHaltTape_eq_assemblySourceRestFinishSourceTape]
  simpa [List.map_cons] using
    preservingCellPassDescription_haltsFrom_nonempty_cells_oneBlank
      (assemblySourceRestBoundaryLeftRev w stage) b rest

theorem scanLeftToBlankLeftDescription_haltsFrom_empty_scanRightToBlankLeftHaltTape
    (leftBase : List (Option Bool)) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (scanRightToBlankLeftHaltTape (none :: leftBase) [])
      (scanLeftToBlankLeftHaltTape leftBase [] [none]) := by
  refine ⟨1, ?_⟩
  constructor <;>
    simp [scanRightToBlankLeftHaltTape,
      scanLeftToBlankLeftHaltTape, scanLeftToBlankLeftDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

theorem scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
      (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) := by
  cases hquote : preservingCellPassCellBits sourceRestBits with
  | nil =>
      rw [assemblySourceRestFinishQuoteBoundaryTape,
        assemblySourceRestFinishLeftBoundaryTape, hquote]
      exact
        scanLeftToBlankLeftDescription_haltsFrom_empty_scanRightToBlankLeftHaltTape
          (List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
  | cons quoteHead quoteTail =>
      rcases exists_reverse_append_singleton_of_cons quoteHead quoteTail with
        ⟨scanRev, current, hscan⟩
      rw [assemblySourceRestFinishQuoteBoundaryTape,
        assemblySourceRestFinishLeftBoundaryTape, hquote, hscan]
      exact
        scanLeftToBlankLeftDescription_haltsFrom_scanRightToBlankLeftHaltTape
          (List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
          scanRev current

theorem assemblySourceRestFinishLeftBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_move_left_move_right_none_right
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)
      []

def assemblySourceRestFinishFromLeftBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanLeftToBlankLeftDescription finish

theorem assemblySourceRestFinishQuoteBoundarySpec_of_leftBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundarySpec finish) :
    AssemblySourceRestFinishQuoteBoundarySpec
      (assemblySourceRestFinishFromLeftBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
          w sourceRestBits stage)
        (assemblySourceRestFinishLeftBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    (h : AssemblySourceRestFinishLeftBoundaryConstruction) :
    AssemblySourceRestFinishQuoteBoundaryConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromLeftBoundary finish,
      assemblySourceRestFinishQuoteBoundarySpec_of_leftBoundary hfinish⟩

def assemblySourceRestFinishFromQuoteBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanRightToBlankLeftDescription finish

theorem assemblySourceRestFinishSpec_of_quoteBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundarySpec finish) :
    AssemblySourceRestFinishSpec
      (assemblySourceRestFinishFromQuoteBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishConstruction_of_quoteBoundary
    (h : AssemblySourceRestFinishQuoteBoundaryConstruction) :
    AssemblySourceRestFinishConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromQuoteBoundary finish,
      assemblySourceRestFinishSpec_of_quoteBoundary hfinish⟩

def assemblySourceRestFinishFromBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical assemblySourceRestFinishLeftMoveDescription finish

theorem assemblySourceRestFinishSpec_of_boundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundarySpec finish) :
    AssemblySourceRestFinishSpec
      (assemblySourceRestFinishFromBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.left
        (assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishConstruction_of_boundary
    (h : AssemblySourceRestFinishBoundaryConstruction) :
    AssemblySourceRestFinishConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromBoundary finish,
      assemblySourceRestFinishSpec_of_boundary hfinish⟩

/--
Core finite-machine obligation for the left-boundary source-rest finish phase.
All surrounding results are exact-tape adapters; this leaf is responsible for
rewriting the mixed parser-stack/source-rest layout into
{name}`assemblySourceRestFinishTargetTape`.
-/
theorem assemblySourceRestFinishLeftBoundaryCoreConstruction :
    AssemblySourceRestFinishLeftBoundaryCoreConstruction := by
  sorry

theorem assemblySourceRestFinishLeftBoundaryConstruction :
    AssemblySourceRestFinishLeftBoundaryConstruction :=
  assemblySourceRestFinishLeftBoundaryConstruction_of_core
    assemblySourceRestFinishLeftBoundaryCoreConstruction

theorem assemblySourceRestFinishQuoteBoundaryConstruction :
    AssemblySourceRestFinishQuoteBoundaryConstruction :=
  assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    assemblySourceRestFinishLeftBoundaryConstruction

theorem assemblySourceRestFinishConstruction :
    AssemblySourceRestFinishConstruction :=
  assemblySourceRestFinishConstruction_of_quoteBoundary
    assemblySourceRestFinishQuoteBoundaryConstruction

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

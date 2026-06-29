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


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Basic

set_option doc.verso true

/-!
# Bounded-layout parser contract

This module contains the public parser-phase tape shapes and specifications.
The concrete finite parser implementation lives in the following parser
submodules, with this file kept small so later finite-machine lemmas can be
split by phase.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def ParsedLayoutBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.DovetailLayout.encode L)

def ParsedLayoutTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.input (ParsedLayoutBits L)

def checkedInputTape (bits : Word Bool) : Tape Bool :=
  match bits with
  | [] => { left := [], head := none, right := [none] }
  | bit :: rest =>
      { left := [], head := some bit, right := rest.map some ++ [none] }

def ParsedLayoutCheckedTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  checkedInputTape (ParsedLayoutBits L)

def ParsedLayoutCheckedHandoffTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.move Direction.right (ParsedLayoutCheckedTape L)

theorem checkedInputTape_normalizedOutput
    (bits : Word Bool) :
    Tape.normalizedOutput (checkedInputTape bits) = bits := by
  cases bits with
  | nil =>
      simp [checkedInputTape, Tape.normalizedOutput, Tape.cells]
  | cons bit rest =>
      have hrest :
          List.filterMap ((fun cell : Option Bool => cell) ∘ some)
              rest = rest := by
        simpa [Function.comp] using Tape.filterMap_id_map_some rest
      simp [checkedInputTape, Tape.normalizedOutput, Tape.cells, hrest]

theorem parsedLayoutCheckedTape_normalizedOutput
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutCheckedTape L) =
      ParsedLayoutBits L :=
  checkedInputTape_normalizedOutput (ParsedLayoutBits L)

theorem parsedLayoutBits_eq_false_false_tail
    (L : MachineDescription.DovetailLayout) :
    exists tail : Word Bool,
      ParsedLayoutBits L = false :: false :: tail := by
  rcases EncodedRewriters.dovetailLayout_encode_cons L with ⟨tail, htail⟩
  refine ⟨false :: true ::
      MachineDescription.encodeCodeWordAsInput tail, ?_⟩
  simp [ParsedLayoutBits, htail, MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]

theorem parsedLayoutCheckedTape_move_left_move_right
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right (ParsedLayoutCheckedTape L)) =
      ParsedLayoutCheckedTape L := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  simp [ParsedLayoutCheckedTape, checkedInputTape, htail, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem parsedLayoutCheckedHandoffTape_move_left
    (L : MachineDescription.DovetailLayout) :
    Tape.move Direction.left (ParsedLayoutCheckedHandoffTape L) =
      ParsedLayoutCheckedTape L := by
  simpa [ParsedLayoutCheckedHandoffTape]
    using parsedLayoutCheckedTape_move_left_move_right L

theorem parsedLayoutCheckedHandoffTape_normalizedOutput
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutCheckedHandoffTape L) =
      ParsedLayoutBits L := by
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, htail⟩
  have htailOut :
      List.filterMap ((fun cell : Option Bool => cell) ∘ some)
          tail = tail := by
    simpa [Function.comp] using Tape.filterMap_id_map_some tail
  simp [ParsedLayoutCheckedHandoffTape, ParsedLayoutCheckedTape,
    checkedInputTape, htail, Tape.move, Tape.moveRight,
    Tape.normalizedOutput, Tape.cells, htailOut]

def LayoutCheckedParserForwardSpec
    (parser : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    parser.HaltsWithTape
      (ParsedLayoutBits L)
      (ParsedLayoutCheckedTape L)

def LayoutCheckedParserClosedSpec
    (parser : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    parser.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        MachineDescription.DovetailLayout.decodeComplete code = some L ∧
          T = ParsedLayoutCheckedTape L

def LayoutCheckedParserSpec
    (parser : MachineDescription) : Prop :=
  ReadySpec parser ∧
    LayoutCheckedParserForwardSpec parser ∧
      LayoutCheckedParserClosedSpec parser

def LayoutCheckedParserConstruction : Prop :=
  exists parser : MachineDescription,
    LayoutCheckedParserSpec parser

def LayoutParserForwardSpec
    (parser : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    parser.HaltsWithTape
      (ParsedLayoutBits L)
      (ParsedLayoutTape L)

def LayoutParserClosedSpec
    (parser : MachineDescription) : Prop :=
  forall code : Word MachineCodeSymbol,
  forall T : Tape Bool,
    parser.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T ->
      exists L : MachineDescription.DovetailLayout,
        MachineDescription.DovetailLayout.decodeComplete code = some L ∧
          T = ParsedLayoutTape L

def LayoutParserSpec
    (parser : MachineDescription) : Prop :=
  ReadySpec parser ∧
    LayoutParserForwardSpec parser ∧
      LayoutParserClosedSpec parser

def LayoutParserConstruction : Prop :=
  exists parser : MachineDescription,
    LayoutParserSpec parser

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

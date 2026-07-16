import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.Layout

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.SplitLayout

open Languages

abbrev Geometry := Scheduler.Layout.Geometry
abbrev Cursor := Scheduler.Layout.Cursor
abbrev Frame := Scheduler.Layout.Frame

def splitMarker : MachineCodeSymbol := .transition

def candidateMarker : MachineCodeSymbol := .moveLeft

def encodeSplitAppend (used remaining : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend used
    (splitMarker ::
      MachineDescription.encodeNatAppend remaining suffix)

def decodeSplit (tokens : Word MachineCodeSymbol) :
    Option ((Nat × Nat) × Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (used, afterUsed) =>
      match afterUsed with
      | marker :: afterMarker =>
          if marker = splitMarker then
            match MachineDescription.decodeNat afterMarker with
            | none => none
            | some (remaining, suffix) =>
                some ((used, remaining), suffix)
          else
            none
      | [] => none

def candidateWord (frame : Frame) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend frame.cursor.selectedFuel
    (GeneratedCode.nestedStageCode frame.input
      frame.cursor.inner frame.cursor.outer)

def encode (frame : Frame) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    Scheduler.Layout.encodeGeometryAppend frame.geometry
      (MachineDescription.encodeNatAppend frame.cursor.round
        (encodeSplitAppend frame.cursor.selectedFuel
          (frame.cursor.round - frame.cursor.selectedFuel)
          (encodeSplitAppend frame.cursor.outer
            (frame.geometry.pairBound frame.cursor.round -
              frame.cursor.outer)
            (encodeSplitAppend frame.cursor.inner
              (frame.geometry.pairBound frame.cursor.round -
                frame.cursor.inner)
              (candidateMarker :: candidateWord frame)))))

def decodeCandidate (tokens : Word MachineCodeSymbol) :
    Option ((Nat × Nat × Nat) × Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (selectedFuel, afterFuel) =>
      match MachineDescription.decodeNat afterFuel with
      | none => none
      | some (outer, afterOuter) =>
          match MachineDescription.decodeNat afterOuter with
          | none => none
          | some (inner, input) =>
              some ((selectedFuel, outer, inner), input)

def decode (tokens : Word MachineCodeSymbol) : Option Frame :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match Scheduler.Layout.decodeGeometry rest with
      | none => none
      | some (geometry, afterGeometry) =>
          match MachineDescription.decodeNat afterGeometry with
          | none => none
          | some (round, afterRound) =>
              match decodeSplit afterRound with
              | none => none
              | some ((selectedFuel, fuelRemaining), afterFuel) =>
                  match decodeSplit afterFuel with
                  | none => none
                  | some ((outer, outerRemaining), afterOuter) =>
                      match decodeSplit afterOuter with
                      | none => none
                      | some ((inner, innerRemaining), afterInner) =>
                          match afterInner with
                          | marker :: afterMarker =>
                              if marker = candidateMarker then
                                match decodeCandidate afterMarker with
                                | none => none
                                | some ((candidateFuel, candidateOuter,
                                    candidateInner), input) =>
                                    if candidateFuel = selectedFuel ∧
                                        candidateOuter = outer ∧
                                        candidateInner = inner ∧
                                        selectedFuel + fuelRemaining = round ∧
                                        outer + outerRemaining =
                                          geometry.pairBound round ∧
                                        inner + innerRemaining =
                                          geometry.pairBound round then
                                      some
                                        { geometry := geometry
                                          cursor :=
                                            { round := round
                                              inner := inner
                                              outer := outer
                                              selectedFuel := selectedFuel }
                                          input := input }
                                    else
                                      none
                              else
                                none
                          | [] => none
  | _ => none

theorem decodeSplit_encodeSplitAppend
    (used remaining : Nat) (suffix : Word MachineCodeSymbol) :
    decodeSplit (encodeSplitAppend used remaining suffix) =
      some ((used, remaining), suffix) := by
  simp [decodeSplit, encodeSplitAppend, splitMarker,
    MachineDescription.decodeNat_encodeNatAppend]

theorem decodeCandidate_candidateWord (frame : Frame) :
    decodeCandidate (candidateWord frame) =
      some ((frame.cursor.selectedFuel, frame.cursor.outer,
        frame.cursor.inner), frame.input) := by
  simp [decodeCandidate, candidateWord, GeneratedCode.nestedStageCode,
    GeneratedCode.stageCode, MachineDescription.decodeNat_encodeNatAppend]

theorem decode_encode (frame : Frame)
    (hvalid : frame.cursor.Valid frame.geometry) :
    decode (encode frame) = some frame := by
  rcases frame with ⟨geometry, cursor, input⟩
  rcases cursor with ⟨round, inner, outer, selectedFuel⟩
  simp only [Scheduler.Layout.Cursor.Valid] at hvalid
  rcases hvalid with ⟨hinner, houter, hfuel⟩
  simp [decode, encode, decodeSplit_encodeSplitAppend,
    decodeCandidate_candidateWord,
    Scheduler.Layout.decodeGeometry_encodeGeometryAppend,
    MachineDescription.decodeNat_encodeNatAppend,
    candidateMarker, Nat.add_sub_of_le hfuel,
    Nat.add_sub_of_le houter, Nat.add_sub_of_le hinner]

theorem encode_injective_of_valid {left right : Frame}
    (hleft : left.cursor.Valid left.geometry)
    (hright : right.cursor.Valid right.geometry)
    (hencode : encode left = encode right) : left = right := by
  have hdecode := congrArg decode hencode
  simpa [decode_encode left hleft, decode_encode right hright] using hdecode

theorem input_equiv_injective_of_valid {left right : Frame}
    (hleft : left.cursor.Valid left.geometry)
    (hright : right.cursor.Valid right.geometry)
    (hsource : Tape.Equiv (Tape.input (encode left))
      (Tape.input (encode right))) : left = right := by
  apply encode_injective_of_valid hleft hright
  have hnormalized := Tape.Equiv.normalizedOutput_eq hsource
  have hleftOutput :
      Tape.normalizedOutput (Tape.input (encode left)) = encode left := by
    simpa [Tape.output] using Tape.normalizedOutput_output (encode left)
  have hrightOutput :
      Tape.normalizedOutput (Tape.input (encode right)) = encode right := by
    simpa [Tape.output] using Tape.normalizedOutput_output (encode right)
  exact hleftOutput.symm.trans (hnormalized.trans hrightOutput)

theorem candidate_marker_is_positional (frame : Frame) :
    encode frame =
      MachineCodeSymbol.header ::
        Scheduler.Layout.encodeGeometryAppend frame.geometry
          (MachineDescription.encodeNatAppend frame.cursor.round
            (encodeSplitAppend frame.cursor.selectedFuel
              (frame.cursor.round - frame.cursor.selectedFuel)
              (encodeSplitAppend frame.cursor.outer
                (frame.geometry.pairBound frame.cursor.round -
                  frame.cursor.outer)
                (encodeSplitAppend frame.cursor.inner
                  (frame.geometry.pairBound frame.cursor.round -
                    frame.cursor.inner)
                  (candidateMarker :: candidateWord frame))))) := by
  rfl

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.SplitLayout

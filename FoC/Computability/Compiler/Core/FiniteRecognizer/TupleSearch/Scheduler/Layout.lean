import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Schedule

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Layout

open Languages

inductive Geometry where
  | unbounded
  | bounded (budget : Nat)
deriving DecidableEq

structure Cursor where
  round : Nat
  inner : Nat
  outer : Nat
  selectedFuel : Nat
deriving DecidableEq

structure Frame where
  geometry : Geometry
  cursor : Cursor
  input : Word MachineCodeSymbol
deriving DecidableEq

def encodeGeometryAppend
    (geometry : Geometry) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  match geometry with
  | .unbounded => MachineCodeSymbol.blank :: suffix
  | .bounded budget =>
      MachineCodeSymbol.zero ::
        MachineDescription.encodeNatAppend budget suffix

def decodeGeometry (tokens : Word MachineCodeSymbol) :
    Option (Geometry × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.blank :: rest => some (.unbounded, rest)
  | MachineCodeSymbol.zero :: rest =>
      match MachineDescription.decodeNat rest with
      | none => none
      | some (budget, suffix) => some (.bounded budget, suffix)
  | _ => none

def encodeCursorAppend
    (cursor : Cursor) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend cursor.round
    (MachineDescription.encodeNatAppend cursor.selectedFuel
      (MachineDescription.encodeNatAppend cursor.outer
        (MachineDescription.encodeNatAppend cursor.inner suffix)))

def decodeCursor (tokens : Word MachineCodeSymbol) :
    Option (Cursor × Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (round, afterRound) =>
      match MachineDescription.decodeNat afterRound with
      | none => none
      | some (selectedFuel, afterSelectedFuel) =>
          match MachineDescription.decodeNat afterSelectedFuel with
          | none => none
          | some (outer, afterOuter) =>
              match MachineDescription.decodeNat afterOuter with
              | none => none
              | some (inner, suffix) =>
                  some (⟨round, inner, outer, selectedFuel⟩, suffix)

def encode (frame : Frame) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeGeometryAppend frame.geometry
      (encodeCursorAppend frame.cursor frame.input)

def decode (tokens : Word MachineCodeSymbol) : Option Frame :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeGeometry rest with
      | none => none
      | some (geometry, afterGeometry) =>
          match decodeCursor afterGeometry with
          | none => none
          | some (cursor, input) => some ⟨geometry, cursor, input⟩
  | _ => none

theorem decodeGeometry_encodeGeometryAppend
    (geometry : Geometry) (suffix : Word MachineCodeSymbol) :
    decodeGeometry (encodeGeometryAppend geometry suffix) =
      some (geometry, suffix) := by
  cases geometry <;>
    simp [decodeGeometry, encodeGeometryAppend,
      MachineDescription.decodeNat_encodeNatAppend]

theorem decodeCursor_encodeCursorAppend
    (cursor : Cursor) (suffix : Word MachineCodeSymbol) :
    decodeCursor (encodeCursorAppend cursor suffix) =
      some (cursor, suffix) := by
  cases cursor
  simp [decodeCursor, encodeCursorAppend,
    MachineDescription.decodeNat_encodeNatAppend]

theorem decode_encode (frame : Frame) :
    decode (encode frame) = some frame := by
  cases frame with
  | mk geometry cursor input =>
      simp [decode, encode, decodeGeometry_encodeGeometryAppend,
        decodeCursor_encodeCursorAppend]

theorem encode_injective {left right : Frame}
    (h : encode left = encode right) : left = right := by
  have hdecode := congrArg decode h
  simpa [decode_encode] using hdecode

def Cursor.initial : Cursor := ⟨0, 0, 0, 0⟩

def Geometry.pairBound (geometry : Geometry) (round : Nat) : Nat :=
  match geometry with
  | .unbounded => round
  | .bounded budget => budget

def Cursor.Valid (geometry : Geometry) (cursor : Cursor) : Prop :=
  cursor.inner ≤ geometry.pairBound cursor.round ∧
    cursor.outer ≤ geometry.pairBound cursor.round ∧
    cursor.selectedFuel ≤ cursor.round

def Cursor.advance (geometry : Geometry) (cursor : Cursor) : Cursor :=
  if cursor.selectedFuel < cursor.round then
    ⟨cursor.round, cursor.inner, cursor.outer, cursor.selectedFuel + 1⟩
  else if cursor.outer < geometry.pairBound cursor.round then
    ⟨cursor.round, cursor.inner, cursor.outer + 1, 0⟩
  else if cursor.inner < geometry.pairBound cursor.round then
    ⟨cursor.round, cursor.inner + 1, 0, 0⟩
  else
    ⟨cursor.round + 1, 0, 0, 0⟩

def Frame.advance (frame : Frame) : Frame :=
  { frame with cursor := frame.cursor.advance frame.geometry }

theorem Cursor.initial_valid (geometry : Geometry) :
    Cursor.initial.Valid geometry := by
  cases geometry <;> simp [Cursor.Valid, Cursor.initial, Geometry.pairBound]

theorem Cursor.advance_valid {geometry : Geometry} {cursor : Cursor}
    (hvalid : cursor.Valid geometry) :
    (cursor.advance geometry).Valid geometry := by
  cases geometry with
  | unbounded =>
      rcases cursor with ⟨round, inner, outer, selectedFuel⟩
      simp only [Cursor.Valid, Geometry.pairBound] at hvalid ⊢
      rcases hvalid with ⟨hinner, houterBound, hfuelBound⟩
      by_cases hfuel : selectedFuel < round
      · simp [Cursor.advance, hfuel]
        lia
      · by_cases houter : outer < round
        · simp [Cursor.advance, Geometry.pairBound, hfuel, houter]
          lia
        · by_cases hinnerStep : inner < round
          · simp [Cursor.advance, Geometry.pairBound, hfuel, houter,
              hinnerStep]
            lia
          · simp [Cursor.advance, Geometry.pairBound, hfuel, houter,
              hinnerStep]
  | bounded budget =>
      rcases cursor with ⟨round, inner, outer, selectedFuel⟩
      simp only [Cursor.Valid, Geometry.pairBound] at hvalid ⊢
      rcases hvalid with ⟨hinner, houterBound, hfuelBound⟩
      by_cases hfuel : selectedFuel < round
      · simp [Cursor.advance, hfuel]
        lia
      · by_cases houter : outer < budget
        · simp [Cursor.advance, Geometry.pairBound, hfuel, houter]
          lia
        · by_cases hinnerStep : inner < budget
          · simp [Cursor.advance, Geometry.pairBound, hfuel, houter,
              hinnerStep]
            lia
          · simp [Cursor.advance, Geometry.pairBound, hfuel, houter,
              hinnerStep]

theorem Cursor.advance_selectedFuel_of_lt
    (geometry : Geometry) (cursor : Cursor)
    (hfuel : cursor.selectedFuel < cursor.round) :
    cursor.advance geometry =
      ⟨cursor.round, cursor.inner, cursor.outer,
        cursor.selectedFuel + 1⟩ := by
  simp [Cursor.advance, hfuel]

theorem Cursor.advance_outer_of_fuel_end
    (geometry : Geometry) (cursor : Cursor)
    (hfuel : cursor.selectedFuel = cursor.round)
    (houter : cursor.outer < geometry.pairBound cursor.round) :
    cursor.advance geometry =
      ⟨cursor.round, cursor.inner, cursor.outer + 1, 0⟩ := by
  simp [Cursor.advance, hfuel, houter]

theorem Cursor.advance_inner_of_fuel_outer_end
    (geometry : Geometry) (cursor : Cursor)
    (hfuel : cursor.selectedFuel = cursor.round)
    (houter : cursor.outer = geometry.pairBound cursor.round)
    (hinner : cursor.inner < geometry.pairBound cursor.round) :
    cursor.advance geometry =
      ⟨cursor.round, cursor.inner + 1, 0, 0⟩ := by
  simp [Cursor.advance, hfuel, houter, hinner]

theorem Cursor.advance_round_of_cube_end
    (geometry : Geometry) (cursor : Cursor)
    (hfuel : cursor.selectedFuel = cursor.round)
    (houter : cursor.outer = geometry.pairBound cursor.round)
    (hinner : cursor.inner = geometry.pairBound cursor.round) :
    cursor.advance geometry = ⟨cursor.round + 1, 0, 0, 0⟩ := by
  simp [Cursor.advance, hfuel, houter, hinner]

theorem Cursor.advance_unbounded_round_end (round : Nat) :
    (⟨round, round, round, round⟩ : Cursor).advance .unbounded =
      ⟨round + 1, 0, 0, 0⟩ := by
  exact Cursor.advance_round_of_cube_end .unbounded _ rfl rfl rfl

theorem Cursor.advance_bounded_round_end (budget round : Nat) :
    (⟨round, budget, budget, round⟩ : Cursor).advance (.bounded budget) =
      ⟨round + 1, 0, 0, 0⟩ := by
  exact Cursor.advance_round_of_cube_end (.bounded budget) _ rfl rfl rfl

theorem Frame.advance_input (frame : Frame) :
    frame.advance.input = frame.input := by
  rfl

theorem Frame.advance_geometry (frame : Frame) :
    frame.advance.geometry = frame.geometry := by
  rfl

def Cursor.candidate (cursor : Cursor) : HiddenFuelCandidate :=
  (cursor.inner, cursor.outer, cursor.selectedFuel)

theorem Cursor.valid_candidate_mem_unbounded
    {cursor : Cursor} (hvalid : cursor.Valid .unbounded) :
    cursor.candidate ∈ unboundedRoundCandidates cursor.round := by
  exact (mem_unboundedRoundCandidates_iff cursor.round cursor.inner
    cursor.outer cursor.selectedFuel).2 hvalid

theorem Cursor.valid_candidate_mem_bounded
    {budget : Nat} {cursor : Cursor}
    (hvalid : cursor.Valid (.bounded budget)) :
    cursor.candidate ∈ boundedRoundCandidates budget cursor.round := by
  exact (mem_boundedRoundCandidates_iff budget cursor.round cursor.inner
    cursor.outer cursor.selectedFuel).2 hvalid

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Layout

import FoC.Computability.MachineBuilder.Encoding

namespace FoC
namespace Computability

namespace Section53RuntimeAction

/-- The finite part of a selected runtime transition.  The unbounded target
state remains serialized on tape. -/
structure Action where
  write : Option Bool
  move : Direction
deriving DecidableEq

namespace Action

def optionBools : List (Option Bool) :=
  [none, some false, some true]

def directions : List Direction :=
  [Direction.left, Direction.right]

theorem optionBools_complete (cell : Option Bool) :
    cell ∈ optionBools := by
  cases cell with
  | none => simp [optionBools]
  | some bit => cases bit <;> simp [optionBools]
  done

theorem directions_complete (move : Direction) :
    move ∈ directions := by
  cases move <;> simp [directions]
  done

def elems : List Action :=
  optionBools.flatMap
    (fun write =>
      directions.map
        (fun move => { write := write, move := move }))

def finite : Foundation.FiniteType Action where
  elems := elems
  complete := by
    intro action
    cases action with
    | mk write move =>
        simp [elems, optionBools_complete write,
          directions_complete move]

end Action

end Section53RuntimeAction

end Computability
end FoC

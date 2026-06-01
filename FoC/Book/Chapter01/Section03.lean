import FoC.Foundation.Logic

namespace FoC
namespace Book
namespace Chapter01
namespace Section03

/-!
Book: Chapter 1, Section 1.3, Application: Logic Circuits.

The circuit drawings and design exercises are classified in coverage as
application material. This module records the reusable formal objects behind
the section's DNF discussion.
-/

open Foundation

inductive Literal (Var : Type u) where
  | positive : Var -> Literal Var
  | negative : Var -> Literal Var

def Literal.eval (valuation : Var -> Bool) : Literal Var -> Bool
  | Literal.positive v => valuation v
  | Literal.negative v => !(valuation v)

def Conjunction.eval (valuation : Var -> Bool) : List (Literal Var) -> Bool
  | [] => true
  | lit :: rest => Literal.eval valuation lit && Conjunction.eval valuation rest

def DNF.eval (valuation : Var -> Bool) : List (List (Literal Var)) -> Bool
  | [] => false
  | clause :: rest => Conjunction.eval valuation clause || DNF.eval valuation rest

def Literal.toPropForm : Literal Var -> PropForm Var
  | Literal.positive v => PropForm.var v
  | Literal.negative v => PropForm.not (PropForm.var v)

def conjunctionToPropForm : List (Literal Var) -> PropForm Var
  | [] => PropForm.truth
  | lit :: rest => PropForm.and (Literal.toPropForm lit) (conjunctionToPropForm rest)

def dnfToPropForm : List (List (Literal Var)) -> PropForm Var
  | [] => PropForm.falsity
  | clause :: rest => PropForm.or (conjunctionToPropForm clause) (dnfToPropForm rest)

-- Book: Chapter 1, Section 1.3, Definition 1.5
theorem conjunctionToPropForm_eval (valuation : Var -> Bool) :
    forall clause, PropForm.eval valuation (conjunctionToPropForm clause) =
      Conjunction.eval valuation clause
  | [] => rfl
  | lit :: rest => by
      cases lit <;>
        simp [conjunctionToPropForm, Conjunction.eval, Literal.toPropForm, Literal.eval,
          PropForm.eval, conjunctionToPropForm_eval valuation rest]

-- Book: Chapter 1, Section 1.3, Theorem 1.3, DNF representation mechanism
theorem dnfToPropForm_eval (valuation : Var -> Bool) :
    forall dnf, PropForm.eval valuation (dnfToPropForm dnf) = DNF.eval valuation dnf
  | [] => rfl
  | clause :: rest => by
      simp [dnfToPropForm, DNF.eval, PropForm.eval,
        conjunctionToPropForm_eval valuation clause, dnfToPropForm_eval valuation rest]

end Section03
end Chapter01
end Book
end FoC

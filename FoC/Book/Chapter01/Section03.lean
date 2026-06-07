import FoC.Foundation.Logic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter01
namespace Section03

/-!
# Chapter 1, Section 1.3: Logic Circuits and DNF

The section relates compound propositions, combinatorial logic circuits, and
input/output tables. This module records that relationship as executable
syntax: circuits have gates and input wires, propositional formulas can be
implemented as circuits, and truth-table rows can be compiled into DNF clauses.

A clause is a list of literals interpreted as an AND gate; a DNF is a list of
clauses interpreted as an OR of those AND gates. The bridge theorems say that
the list representation, the corresponding propositional formula, and the
book's gate-level circuit viewpoint compute the same truth value.
-/

open Foundation

/-!
## Logic Circuits

The circuit syntax models combinatorial circuits: input wires, constant wires,
and the three basic gate types. The theorem {lit}`Circuit.toPropForm_eval` says
that the proposition obtained by labeling every wire computes the same output
as the circuit itself.
-/

inductive Circuit (Var : Type u) where
  | input : Var -> Circuit Var
  | const : Bool -> Circuit Var
  | not : Circuit Var -> Circuit Var
  | and : Circuit Var -> Circuit Var -> Circuit Var
  | or : Circuit Var -> Circuit Var -> Circuit Var

namespace Circuit

def eval (valuation : Var -> Bool) : Circuit Var -> Bool
  | input v => valuation v
  | const b => b
  | not c => !(eval valuation c)
  | and c d => eval valuation c && eval valuation d
  | or c d => eval valuation c || eval valuation d

def toPropForm : Circuit Var -> PropForm Var
  | input v => PropForm.var v
  | const true => PropForm.truth
  | const false => PropForm.falsity
  | not c => PropForm.not (toPropForm c)
  | and c d => PropForm.and (toPropForm c) (toPropForm d)
  | or c d => PropForm.or (toPropForm c) (toPropForm d)

theorem toPropForm_eval (valuation : Var -> Bool) :
    forall c, PropForm.eval valuation (toPropForm c) = eval valuation c
  | input _ => rfl
  | const true => rfl
  | const false => rfl
  | not c => by
      simp [toPropForm, eval, toPropForm_eval valuation c, PropForm.eval]
  | and c d => by
      simp [toPropForm, eval, toPropForm_eval valuation c,
        toPropForm_eval valuation d, PropForm.eval]
  | or c d => by
      simp [toPropForm, eval, toPropForm_eval valuation c,
        toPropForm_eval valuation d, PropForm.eval]

end Circuit

/-!
Every propositional formula can be implemented using only constants, input
wires, and the three gates AND, OR, and NOT. The non-basic connectives are
expanded by the equivalences introduced earlier in the chapter.
-/

def formulaToCircuit : PropForm Var -> Circuit Var
  | PropForm.var v => Circuit.input v
  | PropForm.truth => Circuit.const true
  | PropForm.falsity => Circuit.const false
  | PropForm.not p => Circuit.not (formulaToCircuit p)
  | PropForm.and p q => Circuit.and (formulaToCircuit p) (formulaToCircuit q)
  | PropForm.or p q => Circuit.or (formulaToCircuit p) (formulaToCircuit q)
  | PropForm.imp p q => Circuit.or (Circuit.not (formulaToCircuit p)) (formulaToCircuit q)
  | PropForm.iff p q =>
      let cp := formulaToCircuit p
      let cq := formulaToCircuit q
      Circuit.and (Circuit.or (Circuit.not cp) cq) (Circuit.or (Circuit.not cq) cp)
  | PropForm.xor p q =>
      let cp := formulaToCircuit p
      let cq := formulaToCircuit q
      Circuit.and (Circuit.or cp cq) (Circuit.not (Circuit.and cp cq))

theorem formulaToCircuit_eval (valuation : Var -> Bool) :
    forall p, Circuit.eval valuation (formulaToCircuit p) = PropForm.eval valuation p
  | PropForm.var _ => rfl
  | PropForm.truth => rfl
  | PropForm.falsity => rfl
  | PropForm.not p => by
      simp [formulaToCircuit, Circuit.eval, PropForm.eval, formulaToCircuit_eval valuation p]
  | PropForm.and p q => by
      simp [formulaToCircuit, Circuit.eval, PropForm.eval,
        formulaToCircuit_eval valuation p, formulaToCircuit_eval valuation q]
  | PropForm.or p q => by
      simp [formulaToCircuit, Circuit.eval, PropForm.eval,
        formulaToCircuit_eval valuation p, formulaToCircuit_eval valuation q]
  | PropForm.imp p q => by
      simp [formulaToCircuit, Circuit.eval, PropForm.eval,
        formulaToCircuit_eval valuation p, formulaToCircuit_eval valuation q]
  | PropForm.iff p q => by
      simp [formulaToCircuit, Circuit.eval, PropForm.eval,
        formulaToCircuit_eval valuation p, formulaToCircuit_eval valuation q]
      cases PropForm.eval valuation p <;> cases PropForm.eval valuation q <;> simp
  | PropForm.xor p q => by
      simp [formulaToCircuit, Circuit.eval, PropForm.eval,
        formulaToCircuit_eval valuation p, formulaToCircuit_eval valuation q]
      cases PropForm.eval valuation p <;> cases PropForm.eval valuation q <;> simp

theorem formulaToCircuit_toPropForm_equivalent (p : PropForm Var) :
    PropForm.LogicallyEquivalent (Circuit.toPropForm (formulaToCircuit p)) p := by
  intro valuation
  rw [Circuit.toPropForm_eval, formulaToCircuit_eval]

/-!
The named examples below match the section's displayed circuit expressions and
the XOR blueprint used while building a circuit from a formula.
-/

inductive ThreeInput where
  | first
  | second
  | third
deriving DecidableEq, Repr

namespace ThreeInput

def valuation (firstValue secondValue thirdValue : Bool) : ThreeInput -> Bool
  | first => firstValue
  | second => secondValue
  | third => thirdValue

def firstFormula : PropForm ThreeInput :=
  PropForm.var first

def secondFormula : PropForm ThreeInput :=
  PropForm.var second

def thirdFormula : PropForm ThreeInput :=
  PropForm.var third

def firstWire : Circuit ThreeInput :=
  Circuit.input first

def secondWire : Circuit ThreeInput :=
  Circuit.input second

def thirdWire : Circuit ThreeInput :=
  Circuit.input third

end ThreeInput

open ThreeInput

def figure_1_3_formula : PropForm ThreeInput :=
  PropForm.and
    (PropForm.not firstFormula)
    (PropForm.or secondFormula
      (PropForm.not (PropForm.and firstFormula thirdFormula)))

def figure_1_3_circuit : Circuit ThreeInput :=
  Circuit.and
    (Circuit.not firstWire)
    (Circuit.or secondWire
      (Circuit.not (Circuit.and firstWire thirdWire)))

theorem figure_1_3_circuit_computes_formula :
    PropForm.LogicallyEquivalent
      (Circuit.toPropForm figure_1_3_circuit)
      figure_1_3_formula := by
  intro valuation
  rfl

def xor_blueprint_formula : PropForm ThreeInput :=
  PropForm.xor firstFormula secondFormula

def xor_blueprint_circuit : Circuit ThreeInput :=
  Circuit.and
    (Circuit.or firstWire secondWire)
    (Circuit.not (Circuit.and firstWire secondWire))

theorem xor_blueprint_circuit_matches_xor :
    PropForm.LogicallyEquivalent
      (Circuit.toPropForm xor_blueprint_circuit)
      xor_blueprint_formula := by
  intro valuation
  cases hfirst : valuation first <;>
    cases hsecond : valuation second <;>
    simp [xor_blueprint_circuit, xor_blueprint_formula, firstFormula, secondFormula,
      firstWire, secondWire, Circuit.toPropForm, PropForm.eval, hfirst, hsecond]

def labeled_circuit_formula : PropForm ThreeInput :=
  PropForm.and
    (PropForm.not (PropForm.and firstFormula secondFormula))
    (PropForm.or secondFormula (PropForm.not thirdFormula))

def labeled_circuit : Circuit ThreeInput :=
  Circuit.and
    (Circuit.not (Circuit.and firstWire secondWire))
    (Circuit.or secondWire (Circuit.not thirdWire))

theorem labeled_circuit_computes_formula :
    PropForm.LogicallyEquivalent
      (Circuit.toPropForm labeled_circuit)
      labeled_circuit_formula := by
  intro valuation
  rfl

/-!
# Disjunctive Normal Form

The list definitions below are the computational core of Definition 1.3 and
Theorem 1.1 from the source text.
-/

/-! A literal is either a variable or the negation of a variable. -/
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

/-!
Translating one conjunction of literals into a formula preserves its truth
value under every valuation.
-/
theorem conjunctionToPropForm_eval (valuation : Var -> Bool) :
    forall clause, PropForm.eval valuation (conjunctionToPropForm clause) =
      Conjunction.eval valuation clause
  | [] => rfl
  | lit :: rest => by
      cases lit <;>
        simp [conjunctionToPropForm, Conjunction.eval, Literal.toPropForm, Literal.eval,
          PropForm.eval, conjunctionToPropForm_eval valuation rest]

/-!
The DNF theorem lifts the conjunction result to a disjunction of conjunctions.
This is the semantic core of the section's DNF representation mechanism.
-/
theorem dnfToPropForm_eval (valuation : Var -> Bool) :
    forall dnf, PropForm.eval valuation (dnfToPropForm dnf) = DNF.eval valuation dnf
  | [] => rfl
  | clause :: rest => by
      simp [dnfToPropForm, DNF.eval, PropForm.eval,
        conjunctionToPropForm_eval valuation clause, dnfToPropForm_eval valuation rest]

def rowClause (vars : List Var) (row : Var -> Bool) : List (Literal Var) :=
  vars.map (fun v => if row v then Literal.positive v else Literal.negative v)

def dnfFromRows (vars : List Var) (rows : List (Var -> Bool)) : List (List (Literal Var)) :=
  rows.map (rowClause vars)

/-!
The clause generated from one truth-table row is true exactly when the current
valuation agrees with that row on every listed variable.
-/
theorem rowClause_eval_eq_all (valuation row : Var -> Bool) (vars : List Var) :
    Conjunction.eval valuation (rowClause vars row) =
      vars.all (fun v => valuation v == row v) := by
  induction vars with
  | nil =>
      rfl
  | cons v vars ih =>
      by_cases hv : row v = true
      · cases hval : valuation v
        · simp [rowClause, Conjunction.eval, Literal.eval, hv, hval]
        · simp [rowClause, Conjunction.eval, Literal.eval, hv, hval]
          simpa [rowClause] using ih
      · have hvfalse : row v = false := by
          cases hrow : row v
          · rfl
          · exact False.elim (hv hrow)
        cases hval : valuation v
        · simp [rowClause, Conjunction.eval, Literal.eval, hvfalse, hval]
          simpa [rowClause] using ih
        · simp [rowClause, Conjunction.eval, Literal.eval, hvfalse, hval]

/-!
The DNF generated from all true rows is true exactly when at least one listed
row agrees with the current valuation on all listed variables.
-/
theorem dnfFromRows_eval_eq_any (valuation : Var -> Bool) (vars : List Var)
    (rows : List (Var -> Bool)) :
    DNF.eval valuation (dnfFromRows vars rows) =
      rows.any (fun row => vars.all (fun v => valuation v == row v)) := by
  induction rows with
  | nil =>
      rfl
  | cons row rows ih =>
      change
        (Conjunction.eval valuation (rowClause vars row) ||
            DNF.eval valuation (dnfFromRows vars rows)) =
          (vars.all (fun v => valuation v == row v) ||
            rows.any (fun row => vars.all (fun v => valuation v == row v)))
      rw [rowClause_eval_eq_all valuation row vars, ih]

/-!
The input/output-table example from Figure 1.7 has true rows 001, 011, and
111. The following DNF is exactly the construction in the proof of the DNF
theorem.
-/

def figure_input_output_rows : List (ThreeInput -> Bool) :=
  [valuation false false true, valuation false true true, valuation true true true]

def figure_input_output_dnf : List (List (Literal ThreeInput)) :=
  dnfFromRows [first, second, third] figure_input_output_rows

theorem figure_input_output_dnf_table (a b c : Bool) :
    DNF.eval (valuation a b c) figure_input_output_dnf =
      (c && (!a || b)) := by
  cases a <;> cases b <;> cases c <;>
    rfl

def figure_input_output_simplified_formula : PropForm ThreeInput :=
  PropForm.and
    (PropForm.or
      (PropForm.and (PropForm.not firstFormula) (PropForm.not secondFormula))
      secondFormula)
    thirdFormula

theorem figure_input_output_dnf_simplifies :
    PropForm.LogicallyEquivalent
      (dnfToPropForm figure_input_output_dnf)
      figure_input_output_simplified_formula := by
  intro valuation
  cases hfirst : valuation first <;>
    cases hsecond : valuation second <;>
    cases hthird : valuation third <;>
    simp [figure_input_output_dnf, figure_input_output_rows,
      figure_input_output_simplified_formula, dnfFromRows, rowClause, dnfToPropForm,
      conjunctionToPropForm, Literal.toPropForm, firstFormula, secondFormula,
      thirdFormula, PropForm.eval, hfirst, hsecond, hthird, ThreeInput.valuation]

/-!
Figure 1.8 gives the two input/output tables for adding three binary digits.
The sum bit is true for odd parity; the carry bit is true when at least two
input wires are true.
-/

def fullAdderSumRows : List (ThreeInput -> Bool) :=
  [valuation false false true, valuation false true false, valuation true false false,
    valuation true true true]

def fullAdderCarryRows : List (ThreeInput -> Bool) :=
  [valuation false true true, valuation true false true, valuation true true false,
    valuation true true true]

def fullAdderSumDNF : List (List (Literal ThreeInput)) :=
  dnfFromRows [first, second, third] fullAdderSumRows

def fullAdderCarryDNF : List (List (Literal ThreeInput)) :=
  dnfFromRows [first, second, third] fullAdderCarryRows

def fullAdderSumSpec (a b c : Bool) : Bool :=
  (!a && !b && c) || (!a && b && !c) || (a && !b && !c) || (a && b && c)

def fullAdderCarrySpec (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

theorem fullAdderSumDNF_table (a b c : Bool) :
    DNF.eval (valuation a b c) fullAdderSumDNF = fullAdderSumSpec a b c := by
  cases a <;> cases b <;> cases c <;>
    rfl

theorem fullAdderCarryDNF_table (a b c : Bool) :
    DNF.eval (valuation a b c) fullAdderCarryDNF = fullAdderCarrySpec a b c := by
  cases a <;> cases b <;> cases c <;>
    rfl

/-!
The compact formulas below are the ordinary circuit descriptions of the same
adder: the sum bit is the exclusive-or of the three inputs, and the carry bit
is true when at least two inputs are true.
-/

def fullAdderSumFormula : PropForm ThreeInput :=
  PropForm.xor (PropForm.xor firstFormula secondFormula) thirdFormula

def fullAdderCarryFormula : PropForm ThreeInput :=
  PropForm.or
    (PropForm.and firstFormula secondFormula)
    (PropForm.or
      (PropForm.and firstFormula thirdFormula)
      (PropForm.and secondFormula thirdFormula))

theorem fullAdderSumFormula_table (a b c : Bool) :
    PropForm.eval (valuation a b c) fullAdderSumFormula = fullAdderSumSpec a b c := by
  cases a <;> cases b <;> cases c <;>
    rfl

theorem fullAdderCarryFormula_table (a b c : Bool) :
    PropForm.eval (valuation a b c) fullAdderCarryFormula = fullAdderCarrySpec a b c := by
  cases a <;> cases b <;> cases c <;>
    rfl

theorem fullAdderSumDNF_equivalent_formula :
    PropForm.LogicallyEquivalent (dnfToPropForm fullAdderSumDNF) fullAdderSumFormula := by
  intro valuation
  cases hfirst : valuation first <;>
    cases hsecond : valuation second <;>
    cases hthird : valuation third <;>
    simp [dnfToPropForm_eval, DNF.eval, Conjunction.eval, Literal.eval,
      fullAdderSumDNF, fullAdderSumRows, dnfFromRows, rowClause,
      fullAdderSumFormula, firstFormula, secondFormula, thirdFormula,
      PropForm.eval, ThreeInput.valuation, hfirst, hsecond, hthird]

theorem fullAdderCarryDNF_equivalent_formula :
    PropForm.LogicallyEquivalent (dnfToPropForm fullAdderCarryDNF) fullAdderCarryFormula := by
  intro valuation
  cases hfirst : valuation first <;>
    cases hsecond : valuation second <;>
    cases hthird : valuation third <;>
    simp [dnfToPropForm_eval, DNF.eval, Conjunction.eval, Literal.eval,
      fullAdderCarryDNF, fullAdderCarryRows, dnfFromRows, rowClause,
      fullAdderCarryFormula, firstFormula, secondFormula, thirdFormula,
      PropForm.eval, ThreeInput.valuation, hfirst, hsecond, hthird]

end Section03
end Chapter01
end Book
end FoC

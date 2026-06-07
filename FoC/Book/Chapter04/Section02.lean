import FoC.Grammars.BNF

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section02

/-!
# Chapter 4, Section 4.2: Application - BNF

BNF expressions are formalized as a compact notation that expands to ordinary
grammar right-hand sides. This section checks the expansion rules and records
the book's examples for digits, declarations, English fragments, Java-like
syntax, real-number notation, identifiers, and propositions. The reusable
BNF layer is {module}`FoC.Grammars.BNF`.

The important distinction is that BNF is notation, not a new kind of grammar.
The expansion relation turns BNF expressions into ordinary right-hand sides
for grammar productions.
-/

open Grammars

/-!
## BNF Operators

Sequencing concatenates expansions, alternatives choose one side, optional
items may be omitted or present, and repeated items expand by zero or more
copies. These statements are the core semantics for the examples below.

The theorems in this block are small because they are the operational rules of
the notation. Later examples combine these rules to justify concrete expanded
right-hand sides.
-/

theorem bnf_symbol_expands (s : Symbol terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.symbol s) [s] :=
  BNF.Expr.Expands.symbol s

theorem bnf_sequence_expands {e f : BNF.Expr terminal nonterminal} {x y}
    (hx : BNF.Expr.Expands e x) (hy : BNF.Expr.Expands f y) :
    BNF.Expr.Expands (BNF.Expr.seq e f) (x ++ y) :=
  BNF.Expr.Expands.seq hx hy

theorem bnf_alternative_expands {e f : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands (BNF.Expr.alt e f) rhs) :
    BNF.Expr.Expands e rhs ∨ BNF.Expr.Expands f rhs :=
  (BNF.Expr.alt_expands).mp h

theorem bnf_expands_alternative_left {e f : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands e rhs) :
    BNF.Expr.Expands (BNF.Expr.alt e f) rhs :=
  (BNF.Expr.alt_expands).mpr (Or.inl h)

theorem bnf_optional_empty (e : BNF.Expr terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.optional e) [] :=
  BNF.Expr.optional_empty e

theorem bnf_optional_some {e : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands e rhs) :
    BNF.Expr.Expands (BNF.Expr.optional e) rhs :=
  BNF.Expr.optional_some h

theorem bnf_repeat_empty (e : BNF.Expr terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.many e) [] :=
  BNF.Expr.repeat_empty e

theorem bnf_repeat_cons {e : BNF.Expr terminal nonterminal} {first rest}
    (hfirst : BNF.Expr.Expands e first)
    (hrest : BNF.Expr.Expands (BNF.Expr.many e) rest) :
    BNF.Expr.Expands (BNF.Expr.many e) (first ++ rest) :=
  BNF.Expr.repeat_cons hfirst hrest

theorem bnf_repeat_two {e : BNF.Expr terminal nonterminal} {first second}
    (hfirst : BNF.Expr.Expands e first)
    (hsecond : BNF.Expr.Expands e second) :
    BNF.Expr.Expands (BNF.Expr.many e) (first ++ second) := by
  exact BNF.Expr.repeat_cons hfirst (by
    simpa [List.append_nil] using
      BNF.Expr.repeat_cons hsecond (BNF.Expr.repeat_empty e))

/-!
## Example Vocabulary

The terminal and nonterminal types collect the symbols used across the
section's BNF examples. The expression definitions then translate printed BNF
schemata into Lean syntax trees.

These declarations are a vocabulary table for the examples: terminals are the
tokens that appear in generated strings, while nonterminals name syntactic
categories such as digits, identifiers, and propositions.
-/

inductive BNFExampleTerminal where
  | zero
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | plus
  | minus
  | times
  | divide
  | semicolon
  | andTok
  | who
  | the
  | a
  | man
  | woman
  | dog
  | cat
  | computer
  | runs
  | jumps
  | hides
  | knows
  | loves
  | chases
  | owns
  | ifTok
  | elseTok
  | whileTok
  | lparen
  | rparen
  | lbrace
  | rbrace
  | lbracket
  | rbracket
  | equals
  | dot
  | eTok
  | upperETok
  | underscore
  | letter
  | tryTok
  | catchTok
  | finallyTok
  | trueTok
  | falseTok
  | notTok
  | orTok
  | ident
  | number
deriving DecidableEq

inductive BNFExampleNT where
  | digit
  | type
  | variable
  | sentence
  | simpleSentence
  | nounPart
  | verbPart
  | article
  | noun
  | intransitiveVerb
  | transitiveVerb
  | statement
  | blockStatement
  | ifStatement
  | whileStatement
  | assignmentStatement
  | nullStatement
  | condition
  | expression
  | term
  | factor
  | digitSeq
  | realNumber
  | javaVariable
  | catchClause
  | proposition
  | atomicProposition
  | pv
deriving DecidableEq

def bnfTerminal (t : BNFExampleTerminal) :
    Symbol BNFExampleTerminal BNFExampleNT :=
  Symbol.terminal t

def bnfNonterminal (nt : BNFExampleNT) :
    Symbol BNFExampleTerminal BNFExampleNT :=
  Symbol.nonterminal nt

def bnfTerminalExpr (t : BNFExampleTerminal) :
    BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.symbol (bnfTerminal t)

def bnfNonterminalExpr (nt : BNFExampleNT) :
    BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.symbol (bnfNonterminal nt)

def digitAlternativeExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.zero)
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.one)
      (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.two)
        (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.three)
          (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.four)
            (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.five)
              (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.six)
                (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.seven)
                  (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.eight)
                    (bnfTerminalExpr BNFExampleTerminal.nine)))))))))

def signAlternativeExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.plus)
    (bnfTerminalExpr BNFExampleTerminal.minus)

def declarationExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.type)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.variable)
      (BNF.Expr.optional (bnfTerminalExpr BNFExampleTerminal.semicolon)))

def integerExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.digit)
    (BNF.Expr.many (bnfNonterminalExpr BNFExampleNT.digit))

def englishSentenceExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.simpleSentence)
    (BNF.Expr.many
      (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.andTok)
        (bnfNonterminalExpr BNFExampleNT.simpleSentence)))

def englishNounPartExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.article)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.noun)
      (BNF.Expr.many
        (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.who)
          (bnfNonterminalExpr BNFExampleNT.verbPart))))

def englishVerbPartExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.intransitiveVerb)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.transitiveVerb)
      (bnfNonterminalExpr BNFExampleNT.nounPart))

def englishArticleExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.the)
    (bnfTerminalExpr BNFExampleTerminal.a)

def englishNounExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.man)
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.woman)
      (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.dog)
        (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.cat)
          (bnfTerminalExpr BNFExampleTerminal.computer))))

/-!
The Java-like fragment is intentionally layered. Statements refer to blocks,
conditionals, loops, assignments, and expressions; those pieces are then checked
by concrete expansion examples later in the file.
-/

def javaStatementExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.blockStatement)
    (BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.ifStatement)
      (BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.whileStatement)
        (BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.assignmentStatement)
          (bnfNonterminalExpr BNFExampleNT.nullStatement))))

def javaBlockStatementExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lbrace)
    (BNF.Expr.seq
      (BNF.Expr.many (bnfNonterminalExpr BNFExampleNT.statement))
      (bnfTerminalExpr BNFExampleTerminal.rbrace))

def javaIfStatementExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.ifTok)
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lparen)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.condition)
        (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.rparen)
          (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.statement)
            (BNF.Expr.optional
              (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.elseTok)
                (bnfNonterminalExpr BNFExampleNT.statement)))))))

def javaWhileStatementExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.whileTok)
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lparen)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.condition)
        (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.rparen)
          (bnfNonterminalExpr BNFExampleNT.statement))))

def javaAssignmentStatementExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.variable)
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.equals)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.expression)
        (bnfTerminalExpr BNFExampleTerminal.semicolon)))

def javaAdditiveTermExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.plus)
      (bnfTerminalExpr BNFExampleTerminal.minus))
    (bnfNonterminalExpr BNFExampleNT.term)

def javaExpressionExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.term)
    (BNF.Expr.many javaAdditiveTermExpr)

def javaMultiplicativeFactorExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.times)
      (bnfTerminalExpr BNFExampleTerminal.divide))
    (bnfNonterminalExpr BNFExampleNT.factor)

def javaTermExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.factor)
    (BNF.Expr.many javaMultiplicativeFactorExpr)

def javaFactorExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.ident)
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.number)
      (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lparen)
        (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.expression)
          (bnfTerminalExpr BNFExampleTerminal.rparen))))

def digitSeqExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.digit)
    (BNF.Expr.many (bnfNonterminalExpr BNFExampleNT.digit))

def realFractionExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.dot)
    (bnfNonterminalExpr BNFExampleNT.digitSeq)

def realExponentMarkerExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.eTok)
    (bnfTerminalExpr BNFExampleTerminal.upperETok)

def realExponentExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq realExponentMarkerExpr
    (BNF.Expr.seq (BNF.Expr.optional signAlternativeExpr)
      (bnfNonterminalExpr BNFExampleNT.digitSeq))

def realMantissaExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.digitSeq)
      (BNF.Expr.optional realFractionExpr))
    realFractionExpr

/-!
The numeric examples show how optional signs, repeated digit sequences,
fractional parts, and optional exponents combine into a compact BNF expression
while still expanding to explicit token sequences.
-/

def realNumberExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (BNF.Expr.optional signAlternativeExpr)
    (BNF.Expr.seq realMantissaExpr
      (BNF.Expr.optional realExponentExpr))

def javaVariableTailAtomExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.letter)
    (BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.digit)
      (bnfTerminalExpr BNFExampleTerminal.underscore))

def javaIdentifierExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.letter)
    (BNF.Expr.many javaVariableTailAtomExpr)

def javaVariableFieldExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.dot)
    (bnfTerminalExpr BNFExampleTerminal.ident)

def javaVariableIndexExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lbracket)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.expression)
      (bnfTerminalExpr BNFExampleTerminal.rbracket))

def javaVariableTailExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt javaVariableFieldExpr javaVariableIndexExpr

def javaVariableExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq javaIdentifierExpr
    (BNF.Expr.many javaVariableTailExpr)

def javaCatchClauseExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.catchTok)
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lparen)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.variable)
        (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.rparen)
          (bnfNonterminalExpr BNFExampleNT.blockStatement))))

def javaCatchClausesExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.catchClause)
    (BNF.Expr.many (bnfNonterminalExpr BNFExampleNT.catchClause))

def javaTryCatchExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.tryTok)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.blockStatement)
      (BNF.Expr.seq javaCatchClausesExpr
        (BNF.Expr.optional
          (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.finallyTok)
            (bnfNonterminalExpr BNFExampleNT.blockStatement)))))

def atomicPropositionExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.pv)
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lparen)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.proposition)
        (bnfTerminalExpr BNFExampleTerminal.rparen)))

def propositionConnectiveExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.andTok)
    (bnfTerminalExpr BNFExampleTerminal.orTok)

def propositionOperandExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt atomicPropositionExpr
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.notTok)
      (bnfNonterminalExpr BNFExampleNT.proposition))

def compoundPropositionExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq propositionOperandExpr
    (BNF.Expr.many
      (BNF.Expr.seq propositionConnectiveExpr propositionOperandExpr))

/-!
**Checked Expansions.**

The theorems below prove concrete expansions from the BNF expressions. They
serve as small executable checks that optional parts, repetition, alternatives,
and nested syntax examples behave as the textbook descriptions intend.
-/

theorem bnf_digit_seven_expands :
    BNF.Expr.Expands digitAlternativeExpr [bnfTerminal BNFExampleTerminal.seven] := by
  unfold digitAlternativeExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altLeft
  exact BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.seven)

theorem bnf_sign_plus_expands :
    BNF.Expr.Expands signAlternativeExpr [bnfTerminal BNFExampleTerminal.plus] := by
  exact BNF.Expr.Expands.altLeft
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.plus))

theorem bnf_sign_minus_expands :
    BNF.Expr.Expands signAlternativeExpr [bnfTerminal BNFExampleTerminal.minus] := by
  exact BNF.Expr.Expands.altRight
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.minus))

theorem bnf_declaration_without_semicolon_expands :
    BNF.Expr.Expands declarationExpr
      [bnfNonterminal BNFExampleNT.type, bnfNonterminal BNFExampleNT.variable] := by
  unfold declarationExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.type))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.variable))
      (BNF.Expr.Expands.optionalNone
        (bnfTerminalExpr BNFExampleTerminal.semicolon)))

theorem bnf_declaration_with_semicolon_expands :
    BNF.Expr.Expands declarationExpr
      [bnfNonterminal BNFExampleNT.type, bnfNonterminal BNFExampleNT.variable,
        bnfTerminal BNFExampleTerminal.semicolon] := by
  unfold declarationExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.type))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.variable))
      (BNF.Expr.Expands.optionalSome
        (BNF.Expr.Expands.symbol
          (bnfTerminal BNFExampleTerminal.semicolon))))

theorem bnf_integer_one_digit_expands :
    BNF.Expr.Expands integerExpr [bnfNonterminal BNFExampleNT.digit] := by
  unfold integerExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
    (BNF.Expr.Expands.manyZero
      (bnfNonterminalExpr BNFExampleNT.digit))

theorem bnf_integer_three_digits_expands :
    BNF.Expr.Expands integerExpr
      [bnfNonterminal BNFExampleNT.digit, bnfNonterminal BNFExampleNT.digit,
        bnfNonterminal BNFExampleNT.digit] := by
  unfold integerExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
    (BNF.Expr.repeat_cons
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
        (BNF.Expr.repeat_empty (bnfNonterminalExpr BNFExampleNT.digit))))

theorem bnf_english_sentence_with_and_expands :
    BNF.Expr.Expands englishSentenceExpr
      [bnfNonterminal BNFExampleNT.simpleSentence,
        bnfTerminal BNFExampleTerminal.andTok,
        bnfNonterminal BNFExampleNT.simpleSentence] := by
  unfold englishSentenceExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.simpleSentence))
    (BNF.Expr.repeat_cons
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.andTok))
        (BNF.Expr.Expands.symbol
          (bnfNonterminal BNFExampleNT.simpleSentence)))
      (BNF.Expr.repeat_empty
        (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.andTok)
          (bnfNonterminalExpr BNFExampleNT.simpleSentence))))

theorem bnf_english_noun_part_with_relative_clause_expands :
    BNF.Expr.Expands englishNounPartExpr
      [bnfNonterminal BNFExampleNT.article, bnfNonterminal BNFExampleNT.noun,
        bnfTerminal BNFExampleTerminal.who,
        bnfNonterminal BNFExampleNT.verbPart] := by
  unfold englishNounPartExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.article))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.noun))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.who))
          (BNF.Expr.Expands.symbol
            (bnfNonterminal BNFExampleNT.verbPart)))
        (BNF.Expr.repeat_empty
          (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.who)
            (bnfNonterminalExpr BNFExampleNT.verbPart)))))

theorem bnf_english_transitive_verb_part_expands :
    BNF.Expr.Expands englishVerbPartExpr
      [bnfNonterminal BNFExampleNT.transitiveVerb,
        bnfNonterminal BNFExampleNT.nounPart] := by
  unfold englishVerbPartExpr
  exact BNF.Expr.Expands.altRight
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol
        (bnfNonterminal BNFExampleNT.transitiveVerb))
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.nounPart)))

theorem bnf_english_article_the_expands :
    BNF.Expr.Expands englishArticleExpr [bnfTerminal BNFExampleTerminal.the] := by
  unfold englishArticleExpr
  exact BNF.Expr.Expands.altLeft
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.the))

theorem bnf_english_noun_dog_expands :
    BNF.Expr.Expands englishNounExpr [bnfTerminal BNFExampleTerminal.dog] := by
  unfold englishNounExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altLeft
  exact BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dog)

/-!
The Java statement examples begin with small statements and then scale up to
block nesting and expression precedence. Each theorem chooses the relevant
alternative branch before composing the subexpression expansions.
-/

theorem bnf_java_statement_if_expands :
    BNF.Expr.Expands javaStatementExpr [bnfNonterminal BNFExampleNT.ifStatement] := by
  unfold javaStatementExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altLeft
  exact BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.ifStatement)

theorem bnf_java_block_two_statements_expands :
    BNF.Expr.Expands javaBlockStatementExpr
      [bnfTerminal BNFExampleTerminal.lbrace,
        bnfNonterminal BNFExampleNT.statement,
        bnfNonterminal BNFExampleNT.statement,
        bnfTerminal BNFExampleTerminal.rbrace] := by
  unfold javaBlockStatementExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lbrace))
    (BNF.Expr.Expands.seq
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.statement))
        (BNF.Expr.repeat_cons
          (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.statement))
          (BNF.Expr.repeat_empty
            (bnfNonterminalExpr BNFExampleNT.statement))))
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.rbrace)))

theorem bnf_java_if_with_else_expands :
    BNF.Expr.Expands javaIfStatementExpr
      [bnfTerminal BNFExampleTerminal.ifTok,
        bnfTerminal BNFExampleTerminal.lparen,
        bnfNonterminal BNFExampleNT.condition,
        bnfTerminal BNFExampleTerminal.rparen,
        bnfNonterminal BNFExampleNT.statement,
        bnfTerminal BNFExampleTerminal.elseTok,
        bnfNonterminal BNFExampleNT.statement] := by
  unfold javaIfStatementExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.ifTok))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lparen))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.condition))
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.rparen))
          (BNF.Expr.Expands.seq
            (BNF.Expr.Expands.symbol
              (bnfNonterminal BNFExampleNT.statement))
            (BNF.Expr.Expands.optionalSome
              (BNF.Expr.Expands.seq
                (BNF.Expr.Expands.symbol
                  (bnfTerminal BNFExampleTerminal.elseTok))
                (BNF.Expr.Expands.symbol
                  (bnfNonterminal BNFExampleNT.statement))))))))

theorem bnf_java_assignment_expands :
    BNF.Expr.Expands javaAssignmentStatementExpr
      [bnfNonterminal BNFExampleNT.variable,
        bnfTerminal BNFExampleTerminal.equals,
        bnfNonterminal BNFExampleNT.expression,
        bnfTerminal BNFExampleTerminal.semicolon] := by
  unfold javaAssignmentStatementExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.variable))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.equals))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.expression))
        (BNF.Expr.Expands.symbol
          (bnfTerminal BNFExampleTerminal.semicolon))))

theorem bnf_java_expression_three_terms_expands :
    BNF.Expr.Expands javaExpressionExpr
      [bnfNonterminal BNFExampleNT.term,
        bnfTerminal BNFExampleTerminal.plus,
        bnfNonterminal BNFExampleNT.term,
        bnfTerminal BNFExampleTerminal.minus,
        bnfNonterminal BNFExampleNT.term] := by
  unfold javaExpressionExpr javaAdditiveTermExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.term))
    (BNF.Expr.repeat_cons
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.altLeft
          (BNF.Expr.Expands.symbol
            (bnfTerminal BNFExampleTerminal.plus)))
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.term)))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.altRight
            (BNF.Expr.Expands.symbol
              (bnfTerminal BNFExampleTerminal.minus)))
          (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.term)))
        (BNF.Expr.repeat_empty
          (BNF.Expr.seq
            (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.plus)
              (bnfTerminalExpr BNFExampleTerminal.minus))
            (bnfNonterminalExpr BNFExampleNT.term)))))

theorem bnf_java_term_two_factors_expands :
    BNF.Expr.Expands javaTermExpr
      [bnfNonterminal BNFExampleNT.factor,
        bnfTerminal BNFExampleTerminal.times,
        bnfNonterminal BNFExampleNT.factor] := by
  unfold javaTermExpr javaMultiplicativeFactorExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.factor))
    (BNF.Expr.repeat_cons
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.altLeft
          (BNF.Expr.Expands.symbol
            (bnfTerminal BNFExampleTerminal.times)))
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.factor)))
      (BNF.Expr.repeat_empty
        (BNF.Expr.seq
          (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.times)
            (bnfTerminalExpr BNFExampleTerminal.divide))
          (bnfNonterminalExpr BNFExampleNT.factor))))

theorem bnf_java_parenthesized_factor_expands :
    BNF.Expr.Expands javaFactorExpr
      [bnfTerminal BNFExampleTerminal.lparen,
        bnfNonterminal BNFExampleNT.expression,
        bnfTerminal BNFExampleTerminal.rparen] := by
  unfold javaFactorExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  exact BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lparen))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.expression))
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.rparen)))

/-!
The real-number checks are longer because every optional or repeated component
has to choose a branch. The proofs make those choices explicit: sign, mantissa,
fraction, exponent marker, exponent sign, and exponent digits.
-/

theorem bnf_real_number_decimal_with_exponent_expands :
    BNF.Expr.Expands realNumberExpr
      [bnfTerminal BNFExampleTerminal.minus,
        bnfNonterminal BNFExampleNT.digitSeq,
        bnfTerminal BNFExampleTerminal.dot,
        bnfNonterminal BNFExampleNT.digitSeq,
        bnfTerminal BNFExampleTerminal.eTok,
        bnfTerminal BNFExampleTerminal.plus,
        bnfNonterminal BNFExampleNT.digitSeq] := by
  have hFraction :
      BNF.Expr.Expands realFractionExpr
        [bnfTerminal BNFExampleTerminal.dot,
          bnfNonterminal BNFExampleNT.digitSeq] := by
    unfold realFractionExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dot))
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq))
  have hExponent :
      BNF.Expr.Expands realExponentExpr
        [bnfTerminal BNFExampleTerminal.eTok,
          bnfTerminal BNFExampleTerminal.plus,
          bnfNonterminal BNFExampleNT.digitSeq] := by
    unfold realExponentExpr realExponentMarkerExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.altLeft
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.eTok)))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.optionalSome bnf_sign_plus_expands)
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq)))
  unfold realNumberExpr realMantissaExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.optionalSome bnf_sign_minus_expands)
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.altLeft
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq))
          (BNF.Expr.Expands.optionalSome hFraction)))
      (BNF.Expr.Expands.optionalSome hExponent))

theorem bnf_real_number_leading_decimal_expands :
    BNF.Expr.Expands realNumberExpr
      [bnfTerminal BNFExampleTerminal.dot,
        bnfNonterminal BNFExampleNT.digitSeq] := by
  have hFraction :
      BNF.Expr.Expands realFractionExpr
        [bnfTerminal BNFExampleTerminal.dot,
          bnfNonterminal BNFExampleNT.digitSeq] := by
    unfold realFractionExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dot))
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq))
  unfold realNumberExpr realMantissaExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.optionalNone signAlternativeExpr)
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.altRight hFraction)
      (BNF.Expr.Expands.optionalNone realExponentExpr))

theorem bnf_real_number_upper_exponent_expands :
    BNF.Expr.Expands realNumberExpr
      [bnfNonterminal BNFExampleNT.digitSeq,
        bnfTerminal BNFExampleTerminal.upperETok,
        bnfNonterminal BNFExampleNT.digitSeq] := by
  have hMantissa :
      BNF.Expr.Expands realMantissaExpr
        [bnfNonterminal BNFExampleNT.digitSeq] := by
    unfold realMantissaExpr
    simpa using BNF.Expr.Expands.altLeft
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq))
        (BNF.Expr.Expands.optionalNone realFractionExpr))
  have hExponent :
      BNF.Expr.Expands realExponentExpr
        [bnfTerminal BNFExampleTerminal.upperETok,
          bnfNonterminal BNFExampleNT.digitSeq] := by
    unfold realExponentExpr realExponentMarkerExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.altRight
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.upperETok)))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.optionalNone signAlternativeExpr)
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq)))
  unfold realNumberExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.optionalNone signAlternativeExpr)
    (BNF.Expr.Expands.seq hMantissa
      (BNF.Expr.Expands.optionalSome hExponent))

theorem bnf_java_identifier_letter_digit_underscore_expands :
    BNF.Expr.Expands javaIdentifierExpr
      [bnfTerminal BNFExampleTerminal.letter,
        bnfNonterminal BNFExampleNT.digit,
        bnfTerminal BNFExampleTerminal.underscore] := by
  unfold javaIdentifierExpr javaVariableTailAtomExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.letter))
    (BNF.Expr.repeat_cons
      (BNF.Expr.Expands.altRight
        (BNF.Expr.Expands.altLeft
          (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.altRight
          (BNF.Expr.Expands.altRight
            (BNF.Expr.Expands.symbol
              (bnfTerminal BNFExampleTerminal.underscore))))
        (BNF.Expr.repeat_empty
          (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.letter)
            (BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.digit)
              (bnfTerminalExpr BNFExampleTerminal.underscore))))))

theorem bnf_java_variable_letter_digit_underscore_expands :
    BNF.Expr.Expands javaVariableExpr
      [bnfTerminal BNFExampleTerminal.letter,
        bnfNonterminal BNFExampleNT.digit,
        bnfTerminal BNFExampleTerminal.underscore] := by
  unfold javaVariableExpr
  simpa using BNF.Expr.Expands.seq
    bnf_java_identifier_letter_digit_underscore_expands
    (BNF.Expr.repeat_empty javaVariableTailExpr)

theorem bnf_java_variable_field_expands :
    BNF.Expr.Expands javaVariableExpr
      [bnfTerminal BNFExampleTerminal.letter,
        bnfTerminal BNFExampleTerminal.dot,
        bnfTerminal BNFExampleTerminal.ident] := by
  have hIdentifier :
      BNF.Expr.Expands javaIdentifierExpr
        [bnfTerminal BNFExampleTerminal.letter] := by
    unfold javaIdentifierExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.letter))
      (BNF.Expr.repeat_empty javaVariableTailAtomExpr)
  have hField :
      BNF.Expr.Expands javaVariableTailExpr
        [bnfTerminal BNFExampleTerminal.dot,
          bnfTerminal BNFExampleTerminal.ident] := by
    unfold javaVariableTailExpr javaVariableFieldExpr
    exact BNF.Expr.Expands.altLeft
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dot))
        (BNF.Expr.Expands.symbol
          (bnfTerminal BNFExampleTerminal.ident)))
  unfold javaVariableExpr
  simpa using BNF.Expr.Expands.seq hIdentifier
    (BNF.Expr.repeat_cons hField
      (BNF.Expr.repeat_empty javaVariableTailExpr))

theorem bnf_java_variable_index_expands :
    BNF.Expr.Expands javaVariableExpr
      [bnfTerminal BNFExampleTerminal.letter,
        bnfTerminal BNFExampleTerminal.lbracket,
        bnfNonterminal BNFExampleNT.expression,
        bnfTerminal BNFExampleTerminal.rbracket] := by
  have hIdentifier :
      BNF.Expr.Expands javaIdentifierExpr
        [bnfTerminal BNFExampleTerminal.letter] := by
    unfold javaIdentifierExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.letter))
      (BNF.Expr.repeat_empty javaVariableTailAtomExpr)
  have hIndex :
      BNF.Expr.Expands javaVariableTailExpr
        [bnfTerminal BNFExampleTerminal.lbracket,
          bnfNonterminal BNFExampleNT.expression,
          bnfTerminal BNFExampleTerminal.rbracket] := by
    unfold javaVariableTailExpr javaVariableIndexExpr
    exact BNF.Expr.Expands.altRight
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lbracket))
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.expression))
          (BNF.Expr.Expands.symbol
            (bnfTerminal BNFExampleTerminal.rbracket))))
  unfold javaVariableExpr
  simpa using BNF.Expr.Expands.seq hIdentifier
    (BNF.Expr.repeat_cons hIndex
      (BNF.Expr.repeat_empty javaVariableTailExpr))

theorem bnf_java_variable_field_index_field_expands :
    BNF.Expr.Expands javaVariableExpr
      [bnfTerminal BNFExampleTerminal.letter,
        bnfTerminal BNFExampleTerminal.dot,
        bnfTerminal BNFExampleTerminal.ident,
        bnfTerminal BNFExampleTerminal.lbracket,
        bnfNonterminal BNFExampleNT.expression,
        bnfTerminal BNFExampleTerminal.rbracket,
        bnfTerminal BNFExampleTerminal.dot,
        bnfTerminal BNFExampleTerminal.ident] := by
  have hIdentifier :
      BNF.Expr.Expands javaIdentifierExpr
        [bnfTerminal BNFExampleTerminal.letter] := by
    unfold javaIdentifierExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.letter))
      (BNF.Expr.repeat_empty javaVariableTailAtomExpr)
  have hField :
      BNF.Expr.Expands javaVariableTailExpr
        [bnfTerminal BNFExampleTerminal.dot,
          bnfTerminal BNFExampleTerminal.ident] := by
    unfold javaVariableTailExpr javaVariableFieldExpr
    exact BNF.Expr.Expands.altLeft
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dot))
        (BNF.Expr.Expands.symbol
          (bnfTerminal BNFExampleTerminal.ident)))
  have hIndex :
      BNF.Expr.Expands javaVariableTailExpr
        [bnfTerminal BNFExampleTerminal.lbracket,
          bnfNonterminal BNFExampleNT.expression,
          bnfTerminal BNFExampleTerminal.rbracket] := by
    unfold javaVariableTailExpr javaVariableIndexExpr
    exact BNF.Expr.Expands.altRight
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lbracket))
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.expression))
          (BNF.Expr.Expands.symbol
            (bnfTerminal BNFExampleTerminal.rbracket))))
  unfold javaVariableExpr
  simpa using BNF.Expr.Expands.seq hIdentifier
    (BNF.Expr.repeat_cons hField
      (BNF.Expr.repeat_cons hIndex
        (BNF.Expr.repeat_cons hField
          (BNF.Expr.repeat_empty javaVariableTailExpr))))

/-!
The final examples exercise nested Java and proposition expressions. They are
not new theory; they demonstrate that the BNF constructors compose through
larger concrete examples with alternatives, repetition, and optional clauses.
-/

theorem bnf_java_try_catch_without_finally_expands :
    BNF.Expr.Expands javaTryCatchExpr
      [bnfTerminal BNFExampleTerminal.tryTok,
        bnfNonterminal BNFExampleNT.blockStatement,
        bnfNonterminal BNFExampleNT.catchClause] := by
  have hCatches :
      BNF.Expr.Expands javaCatchClausesExpr
        [bnfNonterminal BNFExampleNT.catchClause] := by
    unfold javaCatchClausesExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.catchClause))
      (BNF.Expr.repeat_empty
        (bnfNonterminalExpr BNFExampleNT.catchClause))
  unfold javaTryCatchExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.tryTok))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol
        (bnfNonterminal BNFExampleNT.blockStatement))
      (BNF.Expr.Expands.seq hCatches
        (BNF.Expr.Expands.optionalNone
          (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.finallyTok)
            (bnfNonterminalExpr BNFExampleNT.blockStatement)))))

theorem bnf_java_try_two_catches_with_finally_expands :
    BNF.Expr.Expands javaTryCatchExpr
      [bnfTerminal BNFExampleTerminal.tryTok,
        bnfNonterminal BNFExampleNT.blockStatement,
        bnfNonterminal BNFExampleNT.catchClause,
        bnfNonterminal BNFExampleNT.catchClause,
        bnfTerminal BNFExampleTerminal.finallyTok,
        bnfNonterminal BNFExampleNT.blockStatement] := by
  have hCatches :
      BNF.Expr.Expands javaCatchClausesExpr
        [bnfNonterminal BNFExampleNT.catchClause,
          bnfNonterminal BNFExampleNT.catchClause] := by
    unfold javaCatchClausesExpr
    simpa using BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.catchClause))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.catchClause))
        (BNF.Expr.repeat_empty
          (bnfNonterminalExpr BNFExampleNT.catchClause)))
  unfold javaTryCatchExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.tryTok))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol
        (bnfNonterminal BNFExampleNT.blockStatement))
      (BNF.Expr.Expands.seq hCatches
        (BNF.Expr.Expands.optionalSome
          (BNF.Expr.Expands.seq
            (BNF.Expr.Expands.symbol
              (bnfTerminal BNFExampleTerminal.finallyTok))
            (BNF.Expr.Expands.symbol
              (bnfNonterminal BNFExampleNT.blockStatement))))))

theorem bnf_java_catch_clause_expands :
    BNF.Expr.Expands javaCatchClauseExpr
      [bnfTerminal BNFExampleTerminal.catchTok,
        bnfTerminal BNFExampleTerminal.lparen,
        bnfNonterminal BNFExampleNT.variable,
        bnfTerminal BNFExampleTerminal.rparen,
        bnfNonterminal BNFExampleNT.blockStatement] := by
  unfold javaCatchClauseExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.catchTok))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lparen))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.variable))
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.symbol
            (bnfTerminal BNFExampleTerminal.rparen))
          (BNF.Expr.Expands.symbol
            (bnfNonterminal BNFExampleNT.blockStatement)))))

theorem bnf_atomic_proposition_parenthesized_expands :
    BNF.Expr.Expands atomicPropositionExpr
      [bnfTerminal BNFExampleTerminal.lparen,
        bnfNonterminal BNFExampleNT.proposition,
        bnfTerminal BNFExampleTerminal.rparen] := by
  unfold atomicPropositionExpr
  exact BNF.Expr.Expands.altRight
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.lparen))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.proposition))
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.rparen))))

theorem bnf_compound_proposition_not_and_expands :
    BNF.Expr.Expands compoundPropositionExpr
      [bnfTerminal BNFExampleTerminal.notTok,
        bnfNonterminal BNFExampleNT.proposition,
        bnfTerminal BNFExampleTerminal.andTok,
        bnfNonterminal BNFExampleNT.pv] := by
  have hNot :
      BNF.Expr.Expands propositionOperandExpr
        [bnfTerminal BNFExampleTerminal.notTok,
          bnfNonterminal BNFExampleNT.proposition] := by
    unfold propositionOperandExpr
    exact BNF.Expr.Expands.altRight
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.notTok))
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.proposition)))
  have hPv :
      BNF.Expr.Expands propositionOperandExpr
        [bnfNonterminal BNFExampleNT.pv] := by
    unfold propositionOperandExpr atomicPropositionExpr
    exact BNF.Expr.Expands.altLeft
      (BNF.Expr.Expands.altLeft
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.pv)))
  have hAndPv :
      BNF.Expr.Expands
        (BNF.Expr.seq propositionConnectiveExpr propositionOperandExpr)
        [bnfTerminal BNFExampleTerminal.andTok,
          bnfNonterminal BNFExampleNT.pv] := by
    unfold propositionConnectiveExpr
    exact BNF.Expr.Expands.seq
      (BNF.Expr.Expands.altLeft
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.andTok)))
      hPv
  unfold compoundPropositionExpr
  simpa using BNF.Expr.Expands.seq
    hNot
    (BNF.Expr.repeat_cons hAndPv
      (BNF.Expr.repeat_empty
        (BNF.Expr.seq propositionConnectiveExpr propositionOperandExpr)))

theorem bnf_compound_proposition_parenthesized_or_not_expands :
    BNF.Expr.Expands compoundPropositionExpr
      [bnfTerminal BNFExampleTerminal.lparen,
        bnfNonterminal BNFExampleNT.proposition,
        bnfTerminal BNFExampleTerminal.rparen,
        bnfTerminal BNFExampleTerminal.orTok,
        bnfTerminal BNFExampleTerminal.notTok,
        bnfNonterminal BNFExampleNT.proposition] := by
  have hParen :
      BNF.Expr.Expands propositionOperandExpr
        [bnfTerminal BNFExampleTerminal.lparen,
          bnfNonterminal BNFExampleNT.proposition,
          bnfTerminal BNFExampleTerminal.rparen] := by
    unfold propositionOperandExpr
    exact BNF.Expr.Expands.altLeft
      bnf_atomic_proposition_parenthesized_expands
  have hNot :
      BNF.Expr.Expands propositionOperandExpr
        [bnfTerminal BNFExampleTerminal.notTok,
          bnfNonterminal BNFExampleNT.proposition] := by
    unfold propositionOperandExpr
    exact BNF.Expr.Expands.altRight
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.notTok))
        (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.proposition)))
  have hOrNot :
      BNF.Expr.Expands
        (BNF.Expr.seq propositionConnectiveExpr propositionOperandExpr)
        [bnfTerminal BNFExampleTerminal.orTok,
          bnfTerminal BNFExampleTerminal.notTok,
          bnfNonterminal BNFExampleNT.proposition] := by
    unfold propositionConnectiveExpr
    exact BNF.Expr.Expands.seq
      (BNF.Expr.Expands.altRight
        (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.orTok)))
      hNot
  unfold compoundPropositionExpr
  simpa using BNF.Expr.Expands.seq
    hParen
    (BNF.Expr.repeat_cons hOrNot
      (BNF.Expr.repeat_empty
        (BNF.Expr.seq propositionConnectiveExpr propositionOperandExpr)))

end Section02
end Chapter04
end Book
end FoC

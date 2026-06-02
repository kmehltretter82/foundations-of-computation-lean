import FoC.Grammars.BNF

namespace FoC
namespace Book
namespace Chapter04
namespace Section02

/-!
Book: Chapter 4, Section 4.2, Application: BNF.
-/

open Grammars

-- Book: Chapter 4, Section 4.2, a BNF symbol expands to its singleton RHS.
theorem bnf_symbol_expands (s : Symbol terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.symbol s) [s] :=
  BNF.Expr.Expands.symbol s

-- Book: Chapter 4, Section 4.2, sequencing concatenates expanded RHS lists.
theorem bnf_sequence_expands {e f : BNF.Expr terminal nonterminal} {x y}
    (hx : BNF.Expr.Expands e x) (hy : BNF.Expr.Expands f y) :
    BNF.Expr.Expands (BNF.Expr.seq e f) (x ++ y) :=
  BNF.Expr.Expands.seq hx hy

-- Book: Chapter 4, Section 4.2, BNF alternatives.
theorem bnf_alternative_expands {e f : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands (BNF.Expr.alt e f) rhs) :
    BNF.Expr.Expands e rhs ∨ BNF.Expr.Expands f rhs :=
  (BNF.Expr.alt_expands).mp h

-- Book: Chapter 4, Section 4.2, BNF alternatives.
theorem bnf_expands_alternative_left {e f : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands e rhs) :
    BNF.Expr.Expands (BNF.Expr.alt e f) rhs :=
  (BNF.Expr.alt_expands).mpr (Or.inl h)

-- Book: Chapter 4, Section 4.2, optional BNF item omitted.
theorem bnf_optional_empty (e : BNF.Expr terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.optional e) [] :=
  BNF.Expr.optional_empty e

-- Book: Chapter 4, Section 4.2, optional BNF item present.
theorem bnf_optional_some {e : BNF.Expr terminal nonterminal} {rhs}
    (h : BNF.Expr.Expands e rhs) :
    BNF.Expr.Expands (BNF.Expr.optional e) rhs :=
  BNF.Expr.optional_some h

-- Book: Chapter 4, Section 4.2, repeated BNF item omitted.
theorem bnf_repeat_empty (e : BNF.Expr terminal nonterminal) :
    BNF.Expr.Expands (BNF.Expr.many e) [] :=
  BNF.Expr.repeat_empty e

-- Book: Chapter 4, Section 4.2, repeated BNF item extended.
theorem bnf_repeat_cons {e : BNF.Expr terminal nonterminal} {first rest}
    (hfirst : BNF.Expr.Expands e first)
    (hrest : BNF.Expr.Expands (BNF.Expr.many e) rest) :
    BNF.Expr.Expands (BNF.Expr.many e) (first ++ rest) :=
  BNF.Expr.repeat_cons hfirst hrest

-- Book: Chapter 4, Section 4.2, two repeated BNF items expand by two `many` steps.
theorem bnf_repeat_two {e : BNF.Expr terminal nonterminal} {first second}
    (hfirst : BNF.Expr.Expands e first)
    (hsecond : BNF.Expr.Expands e second) :
    BNF.Expr.Expands (BNF.Expr.many e) (first ++ second) := by
  exact BNF.Expr.repeat_cons hfirst (by
    simpa [List.append_nil] using
      BNF.Expr.repeat_cons hsecond (BNF.Expr.repeat_empty e))

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
  | equals
  | dot
  | eTok
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

def realExponentExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.eTok)
    (BNF.Expr.seq (BNF.Expr.optional signAlternativeExpr)
      (bnfNonterminalExpr BNFExampleNT.digitSeq))

def realNumberExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (BNF.Expr.optional signAlternativeExpr)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.digitSeq)
      (BNF.Expr.seq (BNF.Expr.optional realFractionExpr)
        (BNF.Expr.optional realExponentExpr)))

def javaVariableTailAtomExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.letter)
    (BNF.Expr.alt (bnfNonterminalExpr BNFExampleNT.digit)
      (bnfTerminalExpr BNFExampleTerminal.underscore))

def javaVariableExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.letter)
    (BNF.Expr.many javaVariableTailAtomExpr)

def javaCatchClauseExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.catchTok)
    (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.lparen)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.variable)
        (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.rparen)
          (bnfNonterminalExpr BNFExampleNT.blockStatement))))

def javaTryCatchExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.tryTok)
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.blockStatement)
      (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.catchClause)
        (BNF.Expr.optional
          (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.finallyTok)
            (bnfNonterminalExpr BNFExampleNT.blockStatement)))))

def atomicPropositionExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.trueTok)
    (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.falseTok)
      (bnfTerminalExpr BNFExampleTerminal.ident))

def propositionConnectiveExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.andTok)
    (bnfTerminalExpr BNFExampleTerminal.orTok)

def compoundPropositionExpr : BNF.Expr BNFExampleTerminal BNFExampleNT :=
  BNF.Expr.seq
    (BNF.Expr.optional (bnfTerminalExpr BNFExampleTerminal.notTok))
    (BNF.Expr.seq (bnfNonterminalExpr BNFExampleNT.atomicProposition)
      (BNF.Expr.many
        (BNF.Expr.seq propositionConnectiveExpr
          (bnfNonterminalExpr BNFExampleNT.atomicProposition))))

-- Book: Chapter 4, Section 4.2, a concrete digit alternative.
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

-- Book: Chapter 4, Section 4.2, sign alternatives.
theorem bnf_sign_plus_expands :
    BNF.Expr.Expands signAlternativeExpr [bnfTerminal BNFExampleTerminal.plus] := by
  exact BNF.Expr.Expands.altLeft
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.plus))

-- Book: Chapter 4, Section 4.2, sign alternatives.
theorem bnf_sign_minus_expands :
    BNF.Expr.Expands signAlternativeExpr [bnfTerminal BNFExampleTerminal.minus] := by
  exact BNF.Expr.Expands.altRight
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.minus))

-- Book: Chapter 4, Section 4.2, optional semicolon omitted.
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

-- Book: Chapter 4, Section 4.2, optional semicolon present.
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

-- Book: Chapter 4, Section 4.2, integer as one digit followed by no repeats.
theorem bnf_integer_one_digit_expands :
    BNF.Expr.Expands integerExpr [bnfNonterminal BNFExampleNT.digit] := by
  unfold integerExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digit))
    (BNF.Expr.Expands.manyZero
      (bnfNonterminalExpr BNFExampleNT.digit))

-- Book: Chapter 4, Section 4.2, integer as one digit followed by two repeats.
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

-- Book: Chapter 4, Section 4.2, English sentence BNF with one `and`.
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

-- Book: Chapter 4, Section 4.2, English noun phrase with a relative clause.
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

-- Book: Chapter 4, Section 4.2, English transitive verb phrase.
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

-- Book: Chapter 4, Section 4.2, English lexical alternatives.
theorem bnf_english_article_the_expands :
    BNF.Expr.Expands englishArticleExpr [bnfTerminal BNFExampleTerminal.the] := by
  unfold englishArticleExpr
  exact BNF.Expr.Expands.altLeft
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.the))

-- Book: Chapter 4, Section 4.2, English lexical alternatives.
theorem bnf_english_noun_dog_expands :
    BNF.Expr.Expands englishNounExpr [bnfTerminal BNFExampleTerminal.dog] := by
  unfold englishNounExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altLeft
  exact BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dog)

-- Book: Chapter 4, Section 4.2, Java statement alternatives.
theorem bnf_java_statement_if_expands :
    BNF.Expr.Expands javaStatementExpr [bnfNonterminal BNFExampleNT.ifStatement] := by
  unfold javaStatementExpr
  apply BNF.Expr.Expands.altRight
  apply BNF.Expr.Expands.altLeft
  exact BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.ifStatement)

-- Book: Chapter 4, Section 4.2, Java block statement with two statements.
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

-- Book: Chapter 4, Section 4.2, Java if statement with optional else present.
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

-- Book: Chapter 4, Section 4.2, Java assignment statement.
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

-- Book: Chapter 4, Section 4.2, expression as three terms separated by
-- plus and minus signs.
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

-- Book: Chapter 4, Section 4.2, term as two factors separated by `*`.
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

-- Book: Chapter 4, Section 4.2, factor as parenthesized expression.
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

-- Book: Chapter 4, Section 4.2, exercise BNF for real numbers.
theorem bnf_real_number_decimal_with_exponent_expands :
    BNF.Expr.Expands realNumberExpr
      [bnfTerminal BNFExampleTerminal.minus,
        bnfNonterminal BNFExampleNT.digitSeq,
        bnfTerminal BNFExampleTerminal.dot,
        bnfNonterminal BNFExampleNT.digitSeq,
        bnfTerminal BNFExampleTerminal.eTok,
        bnfTerminal BNFExampleTerminal.plus,
        bnfNonterminal BNFExampleNT.digitSeq] := by
  unfold realNumberExpr realFractionExpr realExponentExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.optionalSome bnf_sign_minus_expands)
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol (bnfNonterminal BNFExampleNT.digitSeq))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.optionalSome
          (BNF.Expr.Expands.seq
            (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.dot))
            (BNF.Expr.Expands.symbol
              (bnfNonterminal BNFExampleNT.digitSeq))))
        (BNF.Expr.Expands.optionalSome
          (BNF.Expr.Expands.seq
            (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.eTok))
            (BNF.Expr.Expands.seq
              (BNF.Expr.Expands.optionalSome bnf_sign_plus_expands)
              (BNF.Expr.Expands.symbol
                (bnfNonterminal BNFExampleNT.digitSeq)))))))

-- Book: Chapter 4, Section 4.2, exercise BNF for Java-style variables.
theorem bnf_java_variable_letter_digit_underscore_expands :
    BNF.Expr.Expands javaVariableExpr
      [bnfTerminal BNFExampleTerminal.letter,
        bnfNonterminal BNFExampleNT.digit,
        bnfTerminal BNFExampleTerminal.underscore] := by
  unfold javaVariableExpr javaVariableTailAtomExpr
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

-- Book: Chapter 4, Section 4.2, exercise BNF for try/catch syntax.
theorem bnf_java_try_catch_without_finally_expands :
    BNF.Expr.Expands javaTryCatchExpr
      [bnfTerminal BNFExampleTerminal.tryTok,
        bnfNonterminal BNFExampleNT.blockStatement,
        bnfNonterminal BNFExampleNT.catchClause] := by
  unfold javaTryCatchExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.tryTok))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol
        (bnfNonterminal BNFExampleNT.blockStatement))
      (BNF.Expr.Expands.seq
        (BNF.Expr.Expands.symbol
          (bnfNonterminal BNFExampleNT.catchClause))
        (BNF.Expr.Expands.optionalNone
          (BNF.Expr.seq (bnfTerminalExpr BNFExampleTerminal.finallyTok)
            (bnfNonterminalExpr BNFExampleNT.blockStatement)))))

-- Book: Chapter 4, Section 4.2, exercise BNF for a concrete catch clause.
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

-- Book: Chapter 4, Section 4.2, exercise BNF for compound propositions.
theorem bnf_compound_proposition_not_and_expands :
    BNF.Expr.Expands compoundPropositionExpr
      [bnfTerminal BNFExampleTerminal.notTok,
        bnfNonterminal BNFExampleNT.atomicProposition,
        bnfTerminal BNFExampleTerminal.andTok,
        bnfNonterminal BNFExampleNT.atomicProposition] := by
  unfold compoundPropositionExpr propositionConnectiveExpr
  simpa using BNF.Expr.Expands.seq
    (BNF.Expr.Expands.optionalSome
      (BNF.Expr.Expands.symbol (bnfTerminal BNFExampleTerminal.notTok)))
    (BNF.Expr.Expands.seq
      (BNF.Expr.Expands.symbol
        (bnfNonterminal BNFExampleNT.atomicProposition))
      (BNF.Expr.repeat_cons
        (BNF.Expr.Expands.seq
          (BNF.Expr.Expands.altLeft
            (BNF.Expr.Expands.symbol
              (bnfTerminal BNFExampleTerminal.andTok)))
          (BNF.Expr.Expands.symbol
            (bnfNonterminal BNFExampleNT.atomicProposition)))
        (BNF.Expr.repeat_empty
          (BNF.Expr.seq
            (BNF.Expr.alt (bnfTerminalExpr BNFExampleTerminal.andTok)
              (bnfTerminalExpr BNFExampleTerminal.orTok))
            (bnfNonterminalExpr BNFExampleNT.atomicProposition)))))

end Section02
end Chapter04
end Book
end FoC

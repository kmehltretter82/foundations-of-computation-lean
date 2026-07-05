import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Runner
import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.LayoutCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.InitialLayout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.UnaryParser
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Algebra
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product

set_option doc.verso true

/-!
# Finite recognizer programming layer

Public wrapper for the semantic contracts used by finite recognizer
constructions.
-/

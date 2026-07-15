import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Runner
import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.LayoutCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.InitialLayout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.UnaryParser
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Contracts
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Algebra
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.ExactFuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Contracts
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product
import FoC.Computability.Compiler.Core.FiniteRecognizer.ProductContracts
import FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter
import FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreterContracts

set_option doc.verso true

/-!
# Finite recognizer programming layer

Public wrapper for the semantic contracts used by finite recognizer
constructions.
-/

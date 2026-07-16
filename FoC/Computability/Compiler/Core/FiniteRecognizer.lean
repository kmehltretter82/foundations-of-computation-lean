import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Runner
import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.LayoutCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.SerializedShift
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Basic
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Algebra
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Program
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.ExactFuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product
import FoC.Computability.Compiler.Core.FiniteRecognizer.DecodedDescriptionInterpreter

set_option doc.verso true

/-!
# Finite recognizer programming layer

Public wrapper for the exact-fuel runner, product execution, fair tuple search,
and decoded-description interpreter used by the universal-prefix construction.
-/

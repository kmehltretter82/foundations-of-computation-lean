import Lake

/-!
# lakefile

Supporting declarations and helper lemmas for lakefile.
-/

open Lake DSL

package «foc» where
  version := v!"0.1.0"

require verso from git "https://github.com/leanprover/verso.git" @ "v4.30.0"

@[default_target]
lean_lib FoC where

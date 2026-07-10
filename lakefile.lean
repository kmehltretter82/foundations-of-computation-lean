import Lake

/-!
# lakefile

Supporting declarations and helper lemmas for lakefile.
-/

open Lake DSL

package «foc» where
  version := v!"0.1.0"

require verso from git "https://github.com/kmehltretter82/verso.git" @
  "b25f4eeddce59f3decf54c0b63d62b6b3f104598"

@[default_target]
lean_lib FoC where

library_facet docs lib : System.FilePath := do
  let docsJob ← lib.pkg.facet `docs |>.fetch
  docsJob.mapM fun _ => do
    let htmlDir := lib.pkg.buildDir / "literate-html"
    logInfo s!"Documentation written to '{htmlDir}'"
    pure htmlDir

package_facet docs pkg : System.FilePath := do
  let htmlJob ← pkg.facet `literateHtml |>.fetch
  htmlJob.mapM fun _ => do
    let htmlDir := pkg.buildDir / "literate-html"
    logInfo s!"Documentation written to '{htmlDir}'"
    pure htmlDir

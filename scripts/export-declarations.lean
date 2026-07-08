import Lean
import Lean.Meta.Basic
import Lean.Util.CollectAxioms

open Lean

def nameFromString (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => acc.str part) Name.anonymous

def csvEscape (s : String) : String :=
  "\"" ++ s.replace "\"" "\"\"" ++ "\""

def nameStartsWith (pref name : Name) : Bool :=
  let ps := pref.components.map Name.toString
  let ns := name.components.map Name.toString
  ps.isPrefixOf ns

def ConstantInfo.kindString : ConstantInfo -> String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

def ConstantInfo.decl? : ConstantInfo -> Option Declaration
  | .axiomInfo info => some (.axiomDecl info)
  | .defnInfo info => some (.defnDecl info)
  | .thmInfo info => some (.thmDecl info)
  | .opaqueInfo info => some (.opaqueDecl info)
  | _ => none

def coreContext : Core.Context :=
  { fileName := "<export-declarations>"
    fileMap := FileMap.ofString ""
    options := {}
    currRecDepth := 0
    maxRecDepth := 1000
    ref := Syntax.missing
    currNamespace := Name.anonymous
    openDecls := []
    initHeartbeats := 0
    maxHeartbeats := 200000
    quotContext := Name.anonymous
    currMacroScope := 0
    diag := false
    cancelTk? := none
    suppressElabErrors := false
    inheritedTraceOptions := {} }

def coreState (env : Environment) : Core.State :=
  { env := env
    nextMacroScope := 0
    ngen := default
    auxDeclNGen := { namePrefix := `_export, idx := 0, parentIdxs := [] }
    traceState := default
    cache := default
    messages := MessageLog.empty
    infoState := default
    snapshotTasks := #[] }

unsafe def declarationHasSorry (env : Environment) (name : Name) : IO Bool := do
  let action : CoreM (Array Name) := collectAxioms name
  let axioms ← EIO.toIO (fun _ => IO.userError "Lean collectAxioms failed")
    (action.run' coreContext (coreState env))
  pure (axioms.any (· == ``sorryAx))

def moduleOf? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | none => none
  | some idx =>
      if h : idx.toNat < env.header.moduleNames.size then
        some env.header.moduleNames[idx.toNat]
      else
        none

def fileOfModule (modName : String) : String :=
  if modName.startsWith "FoC." then
    (modName.splitOn "." |> String.intercalate "/") ++ ".lean"
  else
    ""

def isGeneratedNameString (s : String) : Bool :=
  s.contains "._@" ||
    s.contains ".match_" ||
    s.contains ".rec_" ||
    s.contains ".below" ||
    s.contains ".brecOn" ||
    s.contains ".noConfusion" ||
    s.contains ".casesOn" ||
    s.contains ".ctorIdx" ||
    s.contains "._sunfold" ||
    s.contains "._unsafe_rec" ||
    s.contains "._flat_ctor" ||
    s.contains ".eq_def" ||
    s.contains ".sizeOf_spec" ||
    (s.splitOn "." |>.any fun part =>
      let suffix := part.drop 3
      part.startsWith "eq_" && !suffix.isEmpty && suffix.all Char.isDigit)

def normalizedLevelName (idx : Nat) : Name :=
  Name.mkSimple s!"u{idx}"

def getNormalizedLevelName (name : Name) : StateM (Array Name) Name := do
  let seen ← get
  match seen.findIdx? (· == name) with
  | some idx => pure (normalizedLevelName idx)
  | none =>
      let idx := seen.size
      set (seen.push name)
      pure (normalizedLevelName idx)

partial def normalizeLevel (level : Level) : StateM (Array Name) Level := do
  match level with
  | .zero => pure .zero
  | .succ l => pure (.succ (← normalizeLevel l))
  | .max a b => pure (.max (← normalizeLevel a) (← normalizeLevel b))
  | .imax a b => pure (.imax (← normalizeLevel a) (← normalizeLevel b))
  | .param n => pure (.param (← getNormalizedLevelName n))
  | .mvar n => pure (.mvar n)

partial def normalizeExprNames (expr : Expr) : StateM (Array Name) Expr := do
  match expr with
  | .bvar i => pure (.bvar i)
  | .fvar id => pure (.fvar id)
  | .mvar id => pure (.mvar id)
  | .sort level => pure (.sort (← normalizeLevel level))
  | .const name levels =>
      pure (.const name (← levels.mapM normalizeLevel))
  | .app f a =>
      pure (.app (← normalizeExprNames f) (← normalizeExprNames a))
  | .lam _ type body binderInfo =>
      pure (.lam Name.anonymous
        (← normalizeExprNames type) (← normalizeExprNames body) binderInfo)
  | .forallE _ type body binderInfo =>
      pure (.forallE Name.anonymous
        (← normalizeExprNames type) (← normalizeExprNames body) binderInfo)
  | .letE _ type value body nondep =>
      pure (.letE Name.anonymous
        (← normalizeExprNames type) (← normalizeExprNames value)
        (← normalizeExprNames body) nondep)
  | .lit lit => pure (.lit lit)
  | .mdata _ body => normalizeExprNames body
  | .proj typeName idx struct =>
      pure (.proj typeName idx (← normalizeExprNames struct))

def ppType (type : Expr) : String :=
  toString type

def normalizedTypeKeyCore (type : Expr) : CoreM String := do
  let (reduced, _) ←
    (Meta.reduce type (explicitOnly := false)
      (skipTypes := false) (skipProofs := false)).run
  let normalized := (normalizeExprNames reduced).run #[] |>.fst
  pure (toString normalized)

unsafe def normalizedTypeKey (env : Environment) (type : Expr) : IO String := do
  try
    EIO.toIO (fun _ => IO.userError "Lean type normalization failed")
      ((normalizedTypeKeyCore type).run' coreContext (coreState env))
  catch _ =>
    pure (toString type)

unsafe def emitDecl (env : Environment) (name : Name) (ci : ConstantInfo) :
    IO String := do
  let modName := (moduleOf? env name).map Name.toString |>.getD ""
  let fileName := fileOfModule modName
  let type := ppType ci.type
  let normalizedType ← normalizedTypeKey env ci.type
  let hasSorry ← declarationHasSorry env name
  let isGenerated := isGeneratedNameString name.toString
  pure <| String.intercalate ","
    [csvEscape name.toString,
     csvEscape (ConstantInfo.kindString ci),
     csvEscape modName,
     csvEscape fileName,
     csvEscape (toString (isPrivateName name)),
     csvEscape (toString isGenerated),
     csvEscape (toString hasSorry),
     csvEscape type,
     csvEscape normalizedType]

unsafe def main (_args : List String) : IO UInt32 := do
  let moduleName := nameFromString (_args.getD 0 "FoC.Computability")
  let prefixName := nameFromString (_args.getD 1 "FoC.Computability")
  let env ← importModules #[{ module := moduleName }] {} 0
  let rows ←
    (SMap.toList env.constants).foldlM (init := (#[] : Array String)) fun rows entry => do
      let (name, ci) := entry
      if nameStartsWith prefixName name then
        pure (rows.push (← emitDecl env name ci))
      else
        pure rows
  IO.println "name,kind,module,file,is_private,is_generated,has_sorry,type,normalized_type"
  for row in Array.qsort rows (fun a b => decide (a < b)) do
    IO.println row
  pure 0

import Lean
import Lean.Meta.Basic
import Lean.Util.CollectAxioms

open Lean

def nameFromString (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => acc.str part) Name.anonymous

def csvEscape (s : String) : String :=
  "\"" ++ s.replace "\"" "\"\"" ++ "\""

def shortNameString (s : String) : String :=
  (s.splitOn ".").getLast?.getD s

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

unsafe def declarationDependsOnSorry (env : Environment) (name : Name) : IO Bool := do
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
    s.contains "._proof_" ||
    s.contains "._simp_" ||
    s.contains "._aux_" ||
    s.contains ".«_aux_" ||
    s.contains ".match_" ||
    s.contains ".rec_" ||
    s.contains ".below" ||
    s.contains ".brecOn" ||
    s.contains ".noConfusion" ||
    s.contains ".casesOn" ||
    s.endsWith ".rec" ||
    s.endsWith ".recOn" ||
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
  let reduced ← Core.betaReduce type
  let normalized := (normalizeExprNames reduced).run #[] |>.fst
  pure (toString normalized)

structure NormalizedType where
  type : String
  ok : Bool
  error : String

def normalizedTypeSkipped : NormalizedType :=
  { type := ""
    ok := false
    error := "not requested" }

unsafe def normalizedTypeKey (env : Environment) (type : Expr) :
    IO NormalizedType := do
  try
    let normalized ← EIO.toIO
      (fun _ => IO.userError "Lean type normalization failed")
      ((normalizedTypeKeyCore type).run' coreContext (coreState env))
    pure { type := normalized, ok := true, error := "" }
  catch err =>
    pure
      { type := ""
        ok := false
        error := toString err }

unsafe def emitDecl (env : Environment) (includeNormalized : Bool)
    (name : Name) (ci : ConstantInfo) :
    IO String := do
  let modName := (moduleOf? env name).map Name.toString |>.getD ""
  let fileName := fileOfModule modName
  let type := ppType ci.type
  let normalizedType ←
    if includeNormalized then
      normalizedTypeKey env ci.type
    else
      pure normalizedTypeSkipped
  let dependsOnSorry ← declarationDependsOnSorry env name
  let isGenerated := isGeneratedNameString name.toString
  pure <| String.intercalate ","
    [csvEscape name.toString,
     csvEscape (shortNameString name.toString),
     csvEscape (ConstantInfo.kindString ci),
     csvEscape modName,
     csvEscape fileName,
     csvEscape (toString (isPrivateName name)),
     csvEscape (toString isGenerated),
     csvEscape (toString dependsOnSorry),
     csvEscape type,
     csvEscape normalizedType.type,
     csvEscape (toString normalizedType.ok),
     csvEscape normalizedType.error]

def usage : String :=
  "Usage: lake env lean --run scripts/export-declarations.lean [MODULE] [PREFIX] [--raw-only] [--progress-every=N] [--no-progress]\n" ++
  "\n" ++
  "MODULE is the module to import, default FoC.Computability.\n" ++
  "PREFIX is the declaration-name prefix to export, default FoC.Computability.\n" ++
  "--raw-only skips normalized_type generation for faster broad exports.\n" ++
  "--progress-every=N logs progress to stderr every N matched declarations.\n" ++
  "--no-progress disables stderr progress logging."

structure ExportOptions where
  moduleName : Name
  prefixName : Name
  includeNormalized : Bool
  progressEvery : Nat

inductive ParsedArgs where
  | options (opts : ExportOptions)
  | help
  | error (msg : String)

def parseArgs (args : List String) : ParsedArgs :=
  let knownFlag (arg : String) : Bool :=
    ["--raw-only", "--no-progress", "-h", "--help"].contains arg ||
      arg.startsWith "--progress-every="
  match args.find? (fun arg => arg.startsWith "--" && !knownFlag arg) with
  | some arg => .error s!"unknown option: {arg}\n\n{usage}"
  | none =>
      if args.contains "-h" || args.contains "--help" then
        .help
      else
        let progressArg? :=
          args.find? (fun arg => arg.startsWith "--progress-every=")
        let progressEvery? :=
          progressArg?.bind fun arg =>
            arg.drop "--progress-every=".length |>.toNat?
        match progressArg?, progressEvery? with
        | some arg, none =>
            .error s!"invalid progress interval: {arg}\n\n{usage}"
        | _, _ =>
            let positionals := args.filter (fun arg => !arg.startsWith "-")
            .options
              { moduleName := nameFromString (positionals.getD 0 "FoC.Computability")
                prefixName := nameFromString (positionals.getD 1 "FoC.Computability")
                includeNormalized := !args.contains "--raw-only"
                progressEvery :=
                  if args.contains "--no-progress" then
                    0
                  else
                    progressEvery?.getD 500 }

def shouldReportProgress (progressEvery processed : Nat) : Bool :=
  progressEvery != 0 && processed != 0 && processed % progressEvery == 0

unsafe def emitRows (env : Environment) (opts : ExportOptions)
    (entries : Array (Name × ConstantInfo)) : IO (Array String) := do
  let total := entries.size
  if opts.progressEvery != 0 then
    IO.eprintln s!"export-declarations: matched {total} declarations"
  let mut rows := #[]
  let mut processed := 0
  for entry in entries do
    let (name, ci) := entry
    rows := rows.push (← emitDecl env opts.includeNormalized name ci)
    processed := processed + 1
    if shouldReportProgress opts.progressEvery processed then
      IO.eprintln s!"export-declarations: processed {processed}/{total}"
  if opts.progressEvery != 0 then
    IO.eprintln s!"export-declarations: processed {processed}/{total}"
  pure rows

unsafe def main (_args : List String) : IO UInt32 := do
  match parseArgs _args with
  | .error msg =>
      IO.eprintln msg
      pure 1
  | .help =>
      IO.println usage
      pure 0
  | .options opts =>
      let env ← importModules #[{ module := opts.moduleName }] {} 0
      let entries :=
        (SMap.toList env.constants).foldl (init := (#[] : Array (Name × ConstantInfo)))
          fun rows entry =>
            if nameStartsWith opts.prefixName entry.1 then
              rows.push entry
            else
              rows
      let rows ← emitRows env opts entries
      IO.println "name,short_name,kind,module,file,is_private,is_generated,depends_on_sorry,type,normalized_type,normalization_ok,normalization_error"
      for row in Array.qsort rows (fun a b => decide (a < b)) do
        IO.println row
      pure 0

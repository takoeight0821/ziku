import Ziku.Syntax

namespace Ziku.ExternalBuiltins

/-!
# External Builtin Loading

Loads and manages external builtin definitions from YAML files.
-/

-- External builtin definition (parsed from file)
structure ExternalBuiltin where
  name : String
  argTypes : List Ty
  resultTy : Ty
  arity : Nat
  schemeCode : String
  deriving Repr

instance : Inhabited ExternalBuiltin where
  default := {
    name := ""
    argTypes := []
    resultTy := .con default "Unit"
    arity := 0
    schemeCode := ""
  }

-- Registry of external builtins
structure BuiltinRegistry where
  builtins : List ExternalBuiltin
  deriving Repr

instance : Inhabited BuiltinRegistry := ⟨{ builtins := [] }⟩
instance : EmptyCollection BuiltinRegistry := ⟨{ builtins := [] }⟩

-- Parse type signature string to list of arg types and result type
def parseTypeSignature (sig : String) : Except String (List Ty × Ty) :=
  let parts := sig.splitOn " -> "
  if parts.length < 1 then
    .error s!"Invalid type signature: {sig}"
  else if parts.length == 1 then
    let resultTy := Ty.con default parts[0]!.trim
    .ok ([], resultTy)
  else
    let argTypes := parts.dropLast.map (fun s => Ty.con default s.trim)
    let resultTy := Ty.con default (parts.getLast!.trim)
    .ok (argTypes, resultTy)

-- Strip quotes from string
private def stripQuotes (s : String) : String :=
  let s := s.trim
  if s.startsWith "\"" && s.endsWith "\"" then
    s.drop 1 |>.dropRight 1
  else
    s

-- Simple state for parsing
structure ParseState where
  remaining : List String
  deriving Inhabited

-- Parse a single builtin entry, returning the builtin and updated state
partial def parseBuiltinEntry (state : ParseState) : IO (Option ExternalBuiltin × ParseState) := do
  let mut name : Option String := none
  let mut typeStr : Option String := none
  let mut arity : Option Nat := none
  let mut schemeCode : String := ""
  let mut remaining := state.remaining
  let mut inScheme := false
  let mut schemeIndent := 0
  let mut done := false

  while !remaining.isEmpty && !done do
    let line := remaining.head!
    remaining := remaining.tail!

    if inScheme then
      let lineIndent := line.takeWhile (· == ' ') |>.length
      if line.trim.isEmpty then
        schemeCode := schemeCode ++ "\n"
      else if lineIndent >= schemeIndent then
        schemeCode := schemeCode ++ line.drop schemeIndent ++ "\n"
      else
        remaining := line :: remaining
        inScheme := false
    else
      let trimmed := line.trim
      if trimmed.startsWith "- name:" then
        if name.isSome then
          remaining := line :: remaining
          done := true
        else
          name := some (trimmed.drop 7 |>.trim)
      else if trimmed.startsWith "name:" then
        name := some (trimmed.drop 5 |>.trim)
      else if trimmed.startsWith "type:" then
        typeStr := some (stripQuotes (trimmed.drop 5))
      else if trimmed.startsWith "arity:" then
        arity := trimmed.drop 6 |>.trim.toNat?
      else if trimmed.startsWith "scheme:" then
        let rest := trimmed.drop 7 |>.trim
        if rest == "|" then
          inScheme := true
          schemeIndent := line.takeWhile (· == ' ') |>.length + 2
        else
          schemeCode := stripQuotes rest
      else if trimmed.startsWith "- " then
        remaining := line :: remaining
        done := true

  let newState : ParseState := { remaining := remaining }

  match name, typeStr, arity with
  | some n, some t, some a =>
    match parseTypeSignature t with
    | .ok (argTys, resultTy) =>
      let builtin : ExternalBuiltin := {
        name := n
        argTypes := argTys
        resultTy := resultTy
        arity := a
        schemeCode := schemeCode.trim
      }
      return (some builtin, newState)
    | .error _ =>
      return (none, newState)
  | _, _, _ =>
    return (none, newState)

-- Parse all builtins from YAML content
partial def parseBuiltinsYaml (content : String) : IO BuiltinRegistry := do
  let lines := content.splitOn "\n"
  let mut builtins : List ExternalBuiltin := []
  let mut remaining := lines

  -- Skip until we find "builtins:"
  while !remaining.isEmpty do
    let line := remaining.head!
    remaining := remaining.tail!
    if line.trim.startsWith "builtins:" then
      break

  -- Parse each builtin entry
  let mut state : ParseState := { remaining := remaining }
  while !state.remaining.isEmpty do
    let line := state.remaining.head!
    if line.trim.isEmpty then
      state := { remaining := state.remaining.tail! }
      continue
    if !line.trim.startsWith "-" && !line.trim.startsWith "name:" then
      state := { remaining := state.remaining.tail! }
      continue
    let (result, newState) ← parseBuiltinEntry state
    state := newState
    match result with
    | some builtin => builtins := builtins ++ [builtin]
    | none => pure ()

  return { builtins := builtins }

-- Load registry from file
def loadBuiltinsFile (path : System.FilePath) : IO BuiltinRegistry := do
  if ← path.pathExists then
    let content ← IO.FS.readFile path
    parseBuiltinsYaml content
  else
    return {}

-- Global registry reference
initialize registryRef : IO.Ref (Option BuiltinRegistry) ← IO.mkRef none

-- Initialize registry from default path
def initRegistry (path : System.FilePath := "stdlib/builtins.yaml") : IO BuiltinRegistry := do
  let reg ← loadBuiltinsFile path
  registryRef.set (some reg)
  return reg

-- Get registry (initializes if needed)
def getRegistry : IO BuiltinRegistry := do
  match ← registryRef.get with
  | some reg => return reg
  | none => initRegistry

-- Check if name is an external builtin
def isExternalBuiltin (name : String) : IO Bool := do
  let reg ← getRegistry
  return reg.builtins.any (·.name == name)

-- Get external builtin info by name
def getExternalBuiltin (name : String) : IO (Option ExternalBuiltin) := do
  let reg ← getRegistry
  return reg.builtins.find? (·.name == name)

-- Get type signature for external builtin
def externalBuiltinTypes (name : String) : IO (Option (List Ty × Ty)) := do
  match ← getExternalBuiltin name with
  | some ext => return some (ext.argTypes, ext.resultTy)
  | none => return none

-- Get arity for external builtin
def externalBuiltinArity (name : String) : IO (Option Nat) := do
  match ← getExternalBuiltin name with
  | some ext => return some ext.arity
  | none => return none

-- Pure (non-IO) access functions
-- These use the `initialize` mechanism which is safe

-- Get registry synchronously (for pure code)
-- Note: Returns empty if not initialized
unsafe def getRegistrySyncImpl : BuiltinRegistry :=
  match unsafeIO registryRef.get with
  | some reg => reg
  | none => {}

@[implemented_by getRegistrySyncImpl]
opaque getRegistrySync : BuiltinRegistry

-- Pure: Check if name is an external builtin
def isExternalBuiltinSync (name : String) : Bool :=
  getRegistrySync.builtins.any (·.name == name)

-- Pure: Get external builtin info by name
def getExternalBuiltinSync (name : String) : Option ExternalBuiltin :=
  getRegistrySync.builtins.find? (·.name == name)

-- Pure: Get type signature for external builtin
def externalBuiltinTypesSync (name : String) : Option (List Ty × Ty) :=
  match getExternalBuiltinSync name with
  | some ext => some (ext.argTypes, ext.resultTy)
  | none => none

-- Pure: Get arity for external builtin
def externalBuiltinAritySync (name : String) : Option Nat :=
  match getExternalBuiltinSync name with
  | some ext => some ext.arity
  | none => none

end Ziku.ExternalBuiltins

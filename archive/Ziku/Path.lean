namespace Ziku.Path

/-!
# Path Resolution

This module provides path resolution utilities for the Ziku module system.
It handles resolving import paths to actual file system paths.
-/

/-- Context for path resolution -/
structure Context where
  /-- Current file's directory (for resolving relative paths) -/
  currentDir : System.FilePath
  /-- Library search paths (searched in order for non-relative imports) -/
  searchPaths : List System.FilePath := []
  deriving Repr, Inhabited

/-- Result of path resolution -/
inductive ResolveResult where
  /-- Path was found and resolved -/
  | found : System.FilePath → ResolveResult
  /-- Path was not found; includes list of paths that were tried -/
  | notFound : List System.FilePath → ResolveResult
  deriving Repr

/-- Check if a string represents an absolute path -/
def isAbsolute (path : String) : Bool :=
  path.startsWith "/"

/-- Check if a string represents a relative path (starts with ./ or ../) -/
def isRelative (path : String) : Bool :=
  path.startsWith "./" || path.startsWith "../"

/-- Resolve an import path to an actual file path.

    Resolution order:
    1. Absolute path → use directly
    2. Relative path (./ or ../) → resolve from currentDir
    3. Otherwise → search in searchPaths, then currentDir
-/
def resolve (ctx : Context) (importPath : String) : IO ResolveResult := do
  -- Absolute path
  if isAbsolute importPath then
    let path := System.FilePath.mk importPath
    if ← path.pathExists then
      return .found path
    else
      return .notFound [path]

  -- Relative path (./ or ../)
  if isRelative importPath then
    let path := ctx.currentDir / importPath
    -- Try to normalize the path
    if ← path.pathExists then
      return .found path
    else
      return .notFound [path]

  -- Search in search paths, then current directory
  let allPaths := ctx.searchPaths ++ [ctx.currentDir]
  let mut tried : List System.FilePath := []
  for searchPath in allPaths do
    let path := searchPath / importPath
    tried := tried ++ [path]
    if ← path.pathExists then
      return .found path

  return .notFound tried

/-- Convert a .ziku path to its corresponding .ziki (signature) path -/
def toSignaturePath (zikuPath : System.FilePath) : System.FilePath :=
  let str := zikuPath.toString
  if str.endsWith ".ziku" then
    System.FilePath.mk ((str.dropEnd 5).toString ++ ".ziki")
  else
    System.FilePath.mk (str ++ ".ziki")

/-- Convert a .ziki path to its corresponding .ziku (implementation) path -/
def toImplementationPath (zikiPath : System.FilePath) : System.FilePath :=
  let str := zikiPath.toString
  if str.endsWith ".ziki" then
    System.FilePath.mk ((str.dropEnd 5).toString ++ ".ziku")
  else
    System.FilePath.mk (str ++ ".ziku")

/-- Get the directory containing a file path -/
def parentDir (path : System.FilePath) : System.FilePath :=
  match path.parent with
  | some p => p
  | none => System.FilePath.mk "."

/-- Create a context from a file path (uses the file's directory as currentDir) -/
def contextFromFile (filePath : System.FilePath) (searchPaths : List System.FilePath := []) : Context :=
  { currentDir := parentDir filePath, searchPaths := searchPaths }

end Ziku.Path

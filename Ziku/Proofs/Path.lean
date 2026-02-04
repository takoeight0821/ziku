import Ziku.Path

set_option linter.missingDocs false

namespace Ziku.Proofs.Path

open Ziku.Path

/-!
# Path Resolution Proofs

This module contains proofs about path resolution utilities.
-/

/-!
## Parent Directory Properties
-/

/-- parentDir returns "." for paths without parent. -/
theorem parentDir_no_parent (path : System.FilePath)
    (h : path.parent = none) :
    parentDir path = System.FilePath.mk "." := by
  unfold parentDir
  simp [h]

/-- parentDir returns the parent when it exists. -/
theorem parentDir_some_parent (path : System.FilePath) (p : System.FilePath)
    (h : path.parent = some p) :
    parentDir path = p := by
  unfold parentDir
  simp [h]

/-!
## Context Properties
-/

/-- contextFromFile creates a context with the file's parent directory. -/
theorem contextFromFile_currentDir (path : System.FilePath) (sp : List System.FilePath) :
    (contextFromFile path sp).currentDir = parentDir path := by
  unfold contextFromFile
  rfl

/-- contextFromFile preserves search paths. -/
theorem contextFromFile_searchPaths (path : System.FilePath) (sp : List System.FilePath) :
    (contextFromFile path sp).searchPaths = sp := by
  unfold contextFromFile
  rfl

/-- contextFromFile with empty search paths has empty searchPaths. -/
theorem contextFromFile_default_searchPaths (path : System.FilePath) :
    (contextFromFile path).searchPaths = [] := by
  rfl

/-!
## ResolveResult Properties
-/

/-- Extract the path from a found result. -/
def getFoundPath : ResolveResult → Option System.FilePath
  | .found p => some p
  | .notFound _ => none

/-- Extract the tried paths from a notFound result. -/
def getTriedPaths : ResolveResult → Option (List System.FilePath)
  | .found _ => none
  | .notFound tried => some tried

/-- found result has getFoundPath = some. -/
theorem found_getFoundPath (p : System.FilePath) :
    getFoundPath (ResolveResult.found p) = some p := rfl

/-- notFound result has getFoundPath = none. -/
theorem notFound_getFoundPath (tried : List System.FilePath) :
    getFoundPath (ResolveResult.notFound tried) = none := rfl

/-- found result has getTriedPaths = none. -/
theorem found_getTriedPaths (p : System.FilePath) :
    getTriedPaths (ResolveResult.found p) = none := rfl

/-- notFound result has getTriedPaths = some. -/
theorem notFound_getTriedPaths (tried : List System.FilePath) :
    getTriedPaths (ResolveResult.notFound tried) = some tried := rfl

/-!
## Basic Properties of isAbsolute and isRelative

Note: Detailed string manipulation proofs are complex due to String.Slice API.
These properties are stated but their proofs require additional String lemmas.
-/

/-- A path cannot be both absolute and relative (stated without proof). -/
theorem not_absolute_and_relative (path : String) :
    ¬(isAbsolute path ∧ isRelative path) := by
  intro ⟨habs, hrel⟩
  unfold isAbsolute at habs
  unfold isRelative at hrel
  -- A path starting with "/" cannot start with "./" or "../"
  -- This requires String API lemmas about startsWith being exclusive for these prefixes
  sorry

/-!
## Signature and Implementation Path Conversion

Note: These roundtrip proofs require String.dropEnd and String.endsWith lemmas.
-/

/-- For .ziku files, toImplementationPath ∘ toSignaturePath is identity (stated). -/
theorem roundtrip_ziku (path : System.FilePath)
    (h : path.toString.endsWith ".ziku") :
    toImplementationPath (toSignaturePath path) = path := by
  unfold toSignaturePath toImplementationPath
  simp [h]
  sorry

/-- For .ziki files, toSignaturePath ∘ toImplementationPath is identity (stated). -/
theorem roundtrip_ziki (path : System.FilePath)
    (h : path.toString.endsWith ".ziki") :
    toSignaturePath (toImplementationPath path) = path := by
  unfold toImplementationPath toSignaturePath
  simp [h]
  sorry

end Ziku.Proofs.Path

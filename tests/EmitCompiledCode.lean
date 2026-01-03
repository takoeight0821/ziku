import Ziku.Parser
import Ziku.Elaborate
import Ziku.Translate
import Ziku.Backend.Scheme

/-- Discover test files in a directory by scanning for .ziku files -/
def discoverTests (dir : System.FilePath) : IO (List String) := do
  try
    let entries ← dir.readDir
    let zikuFiles := entries.filterMap fun entry =>
      let name := entry.fileName
      if name.endsWith ".ziku" then
        some (name.dropRight 5)
      else
        none
    pure (zikuFiles.toList.mergeSort (· < ·))
  catch _ =>
    pure []

/-- Generate IR translation output -/
def generateTranslateOutput (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translate elaborated with
      | .ok producer => .ok producer.toString
      | .error e => .error s!"Translation error: {e}"
    | .error e => .error s!"Elaboration error: {e}"
  | .error e => .error e

/-- Generate Scheme code -/
def generateSchemeOutput (input : String) : Except String String :=
  match Ziku.parseExprString input.trim with
  | .ok expr =>
    match Ziku.elaborateAll expr with
    | .ok elaborated =>
      match Ziku.Translate.translate elaborated with
      | .ok producer =>
        .ok (Ziku.Backend.Scheme.compileProducer producer)
      | .error e => .error s!"Translation error: {e}"
    | .error e => .error s!"Elaboration error: {e}"
  | .error e => .error e

/-- Emit translate IR files -/
def emitTranslate : IO Unit := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let emitDir := "tests/emit/translate"
  let tests ← discoverTests sourceDir

  IO.println s!"Emitting translate IR..."

  IO.FS.createDirAll emitDir

  let mut updated := 0
  let mut errors := 0

  for baseName in tests do
    let inputPath := s!"{sourceDir}/{baseName}.ziku"
    let emitPath := s!"{emitDir}/{baseName}.ir"

    let input ← IO.FS.readFile inputPath
    match generateTranslateOutput input with
    | .ok output =>
      IO.FS.writeFile emitPath output
      IO.println s!"  ✓ {baseName}"
      updated := updated + 1
    | .error e =>
      IO.println s!"  ✗ {baseName}: {e}"
      errors := errors + 1

  IO.println s!"Emitted: {updated}, Errors: {errors}"

/-- Emit Scheme code files -/
def emitScheme : IO Unit := do
  let sourceDir := System.FilePath.mk "tests/golden/ir-eval/success"
  let emitDir := "tests/emit/scheme-codegen"
  let tests ← discoverTests sourceDir

  IO.println s!"Emitting Scheme code..."

  IO.FS.createDirAll emitDir

  let mut updated := 0
  let mut errors := 0

  for baseName in tests do
    let inputPath := s!"{sourceDir}/{baseName}.ziku"
    let emitPath := s!"{emitDir}/{baseName}.ss"

    let input ← IO.FS.readFile inputPath
    match generateSchemeOutput input with
    | .ok output =>
      IO.FS.writeFile emitPath output
      IO.println s!"  ✓ {baseName}"
      updated := updated + 1
    | .error e =>
      IO.println s!"  ✗ {baseName}: {e}"
      errors := errors + 1

  IO.println s!"Emitted: {updated}, Errors: {errors}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["translate"] =>
    emitTranslate
    pure 0
  | ["scheme"] =>
    emitScheme
    pure 0
  | ["all"] | [] =>
    emitTranslate
    IO.println ""
    emitScheme
    pure 0
  | _ =>
    IO.println "Usage: emit-compiled-code [translate|scheme|all]"
    IO.println "  translate - Emit IR translation files (.ir)"
    IO.println "  scheme    - Emit Scheme code files (.ss)"
    IO.println "  all       - Emit all compiled code (default)"
    pure 1

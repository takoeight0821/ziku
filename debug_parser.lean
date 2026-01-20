import Ziku.Parser

def main : IO Unit := do
  let input := "def strLen : String -> Int = @(\"scheme\", \"string-length\")\n\ndata Vector a = @(\"scheme\", \"vector\")\n\ndef print : ~String -> Unit = @(\"scheme\", \"display\") | @(\"c\", \"printf\")\n"
  match Ziku.parseProgram input with
  | .ok decls => IO.println s!"Success: {decls}"
  | .error e => IO.println s!"Program Error: {e}"
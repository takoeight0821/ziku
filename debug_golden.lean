import Ziku.Parser

def main : IO Unit := do
  let input := "def strLen : String -> Int = @(\"scheme\", \"string-length\")\n\ndata Vector a = @(\"scheme\", \"vector\")\n\ndef print : ~String -> Unit = @(\"scheme\", \"display\") | @(\"c\", \"printf\")\n"
  
  IO.println s!"Input starts with: {input.trim.take 10}"
  
  match Ziku.parseProgram input.trim with
  | .ok decls => IO.println s!"Success: {decls}"
  | .error e => 
      IO.println s!"Program Error: {e}"
      match Ziku.parseExprString input.trim with
      | .ok expr => IO.println s!"Expr Success: {expr}"
      | .error e => IO.println s!"Expr Error: {e}"

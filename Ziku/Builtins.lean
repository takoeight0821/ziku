import Ziku.Syntax

namespace Ziku

/-!
# Built-in Functions

This module contains shared utilities for built-in functions used by both
the type inference and translation phases.
-/

-- Get builtin enum from name
/-- Returns the 'Builtin' enum variant for a given function name, if it is a built-in. -/
def nameToBuiltin : String → Option Builtin
  | "strLen"    => some .strLen
  | "strAt"     => some .strAt
  | "strSub"    => some .strSub
  | "strToInt"  => some .strToInt
  | "intToStr"  => some .intToStr
  | "runeToStr" => some .runeToStr
  | "intToRune" => some .intToRune
  | "runeToInt" => some .runeToInt
  | "readLine"  => some .readLine
  | "println"   => some .println
  | _           => none

-- Get arity of builtin function
/-- Returns the expected number of arguments for a given built-in function. -/
def builtinArity : Builtin → Nat
  | .strLen    => 1
  | .strAt     => 2
  | .strSub    => 3
  | .strToInt  => 1
  | .intToStr  => 1
  | .runeToStr => 1
  | .intToRune => 1
  | .runeToInt => 1
  | .readLine  => 1
  | .println   => 1

-- Check if a name is a builtin function and return its type signature
-- Returns (argTypes, resultType) for the builtin
/-- Returns the type signature (argument types and return type) for a given built-in function name. -/
def builtinTypes : String → Option (List Ty × Ty)
  | "strLen"    => some ([.con default "String"], .con default "Int")
  | "strAt"     => some ([.con default "String", .con default "Int"], .con default "Rune")
  | "strSub"    => some ([.con default "String", .con default "Int", .con default "Int"], .con default "String")
  | "strToInt"  => some ([.con default "String"], .con default "Int")
  | "intToStr"  => some ([.con default "Int"], .con default "String")
  | "runeToStr" => some ([.con default "Rune"], .con default "String")
  | "intToRune" => some ([.con default "Int"], .con default "Rune")
  | "runeToInt" => some ([.con default "Rune"], .con default "Int")
  | "readLine"  => some ([.con default "Unit"], .con default "String")
  | "println"   => some ([.con default "String"], .con default "Unit")
  | _           => none

-- Collect all curried arguments from a chain of applications
-- e.g., ((f x) y) z  =>  (f, [x, y, z])
/-- Flattens a chain of curried function applications into the base function and a list of arguments. -/
def collectAppArgs : Expr → (Expr × List Expr)
  | .app _ fn arg _ =>
    let (base, args) := collectAppArgs fn
    (base, args ++ [arg])
  | e => (e, [])

end Ziku

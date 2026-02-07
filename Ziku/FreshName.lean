import Ziku.Syntax

namespace Ziku.FreshName

open Ziku (Ident)

/-- Prefix for compiler-generated names. Uses `#` which is not valid in user identifiers. -/
def hygienicPrefix : String := "#"

/-- Generate a fresh hygienic name: `#base{counter}`. -/
def fresh (base : String) (counter : Nat) : Ident :=
  s!"{hygienicPrefix}{base}{counter}"

/-- Generate a static hygienic name: `#name`. -/
def static (name : String) : Ident :=
  s!"{hygienicPrefix}{name}"

/-- Pseudo-constructor for wildcard patterns. -/
def wildCon : Ident := static "wild"

/-- Pseudo-constructor for variable patterns. -/
def varCon : Ident := static "var"

/-- Prefix for literal integer pseudo-constructors. -/
def litIntPrefix : String := static "lit_int_"

/-- Prefix for literal boolean pseudo-constructors. -/
def litBoolPrefix : String := static "lit_bool_"

/-- Prefix for literal string pseudo-constructors. -/
def litStringPrefix : String := static "lit_string_"

/-- Prefix for literal rune pseudo-constructors. -/
def litRunePrefix : String := static "lit_rune_"

/-- Prefix for literal float pseudo-constructors. -/
def litFloatPrefix : String := static "lit_float_"

/-- Pseudo-constructor for unit literal. -/
def litUnit : Ident := static "lit_unit"

/-- General prefix for all literal pseudo-constructors. -/
def litPrefix : String := static "lit_"

/-- Pseudo-constructor for unrecognized literal kinds. -/
def litOther : Ident := static "lit_other"

end Ziku.FreshName

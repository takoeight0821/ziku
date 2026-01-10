-- This module serves as the root of the `Ziku` library.
-- Import modules here that should be built as part of the library.
import Ziku.Syntax
import Ziku.Builtins
import Ziku.IR.Syntax
import Ziku.IR.Eval
import Ziku.Translate
import Ziku.Lexer
import Ziku.Type
import Ziku.Parser
import Ziku.Elaborate
import Ziku.Infer
import Ziku.Backend.Scheme
import Ziku.Proofs.Eval
import Ziku.Proofs.Arithmetic
import Ziku.Proofs.Identities
import Ziku.Proofs.Soundness

/-
my belief is that Qq has some problems with typing.
its not actually easy to make typed metaprogramming work, and Qq doesn't cut it.
something with an indexed datatype breaks things.
see ppTermImpl, try to reproduce the problem here with less
-/

import Qq
import Lean
open Lean Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

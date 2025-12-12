import Lean
import Qq

open Lean hiding Term
open Elab Meta Term Meta Qq Command Match PrettyPrinter Delaborator SubExpr

namespace QuotTerm


-----------------------------------------------------------------------------
---- fancy syntax -----------------------------------------------------------
-----------------------------------------------------------------------------

-- declare_syntax_cat lambda_scope
-- syntax ident : lambda_scope

-- this really does have to be a big number or some syntax doesn't work
syntax:1500 (name := lambda_scoper) "<" term:100 ">" : term

@[term_elab lambda_scoper]
def elabTerm : TermElab := fun stx _typ? => do
  let `(< $t >) := stx | throwError "error"
  -- elabTermImpl stx ctx []
  -- let res <- (elabTermImplS stx [])
  let thing <- `(fun x : Nat => $t == 10)
  Term.elabTerm thing (Option.some q(Nat))

def test_thing : Nat -> Bool := < _ >

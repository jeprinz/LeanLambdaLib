import Qq
import Lean

open Lean hiding Term
open Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

/-
in this file, i'm going to implement a macro or elaborator
which can dispatch proving that the expected an actual types are equal to a tactic.
there is the convert tactic in mathlib, but it seems to call congr, which makes
assumptions about how to prove the equality that i don't want.
-/

/-
first, i'm going to design a test case that gets at the non-trivial behaviour that i need.
in general, it should be possible to pass in a type with unification variables,
solve some of the unification variables during the tactic, and then
make use of that resulting knowledge to typecheck the rest of the term.
-/
axiom T : Type
axiom t1 : T
axiom t2 : T
axiom eq : t1 = t2
axiom P : T → Nat → Type
axiom pt1 : P t1 10
axiom Q : Nat → Type
axiom f : ∀ {n}, P t1 n → Q n → True

/-
so for example, if i have
f (pt1 >>> simp [eq]) _
then the hole should have type (Q 10)
-/

-- first i can check if this is possible using cast and by

#check cast

def test := f (cast (by sorry) pt1) _

-----------------------------------------------------------------------

syntax:1500 (name := cast_scoper) term:10 ">>>" tactic:10 : term

#check Lean.Parser.Term.byTactic

#check Eq.rec

-- referenced similar mathlib tactic
--  https://github.com/leanprover-community/mathlib4/blob/c8989d96db0146e5fa90f13806f341ea81a0da03/Mathlib/Tactic/Convert.lean#L18-L36
@[term_elab cast_scoper]
def elabCast : TermElab := fun stx typ? => do
  -- the next 4 lines of stuff from https://leanprover-community.github.io/lean4-metaprogramming-book/main/07_elaboration.html
  tryPostponeIfNoneOrMVar typ?
  -- If we haven't found the type after postponing just error
  let some expected := typ? | throwError "expected type must be known"
  if expected.isMVar then
    throwError "expected type must be known"

  let `($syn >>> $tac) := stx | throwError "error"
  let exp <- Term.elabTerm syn typ?
  let actual <- inferType exp
  -- elabTermImpl stx ctx []
  -- let res <- (elabTermImplS stx [])
  -- let res <- `(1 + 2)
  -- Term.elabTerm res (Option.some expected)
  return _

import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic

open QuotTerm

-- doing typechecking with the normal verion that represents terms as mappings from the context,
-- SP is needed. but that shouldn't be true if i just freevars in the QTerms.
-- lets see how this works out.

namespace S
-- contexts
abbrev nil := <Nil>
abbrev cons := <Cons> -- takes ctx, lvl, and type


abbrev pi (A B : QTerm) := app (app <Pi> A) (lam "a" B)
abbrev U := <U>
end S

inductive Var : QTerm → QTerm → Nat → Prop where
| zero : ∀{ctx T},
  Var <{S.cons} {ctx} {T}> (lift 0 T) 0
| succ : ∀{ctx A T s}, Var ctx A s
  → Var <{S.cons} {ctx} {T}> (lift 0 A) s.succ

-- context → level → type → term → prop
inductive Typed : QTerm → QTerm → QTerm → Prop where
| lambda : ∀{ctx A B s},
  Typed <{S.cons} {ctx} {A}> B s
  → Typed ctx (S.pi A B) (lam "x" s)
| alambda : ∀{ctx A B s},
  Typed ctx S.U A
  → Typed <{S.cons} {ctx} {A}> B s
  → Typed ctx (S.pi A B) (lam "y" s)
| app : ∀{ctx A B s1 s2}, Typed ctx (S.pi A B) s1 → Typed ctx A s2
  → Typed ctx (subst 0 s2 B) (app s1 s2)
| var : ∀{ctx T t}, Var ctx T t → Typed ctx T (var t)
| U : ∀{ctx}, Typed ctx S.U S.U
| Pi : ∀{ctx A B}, Typed ctx S.U A
  → Typed <{S.cons} {ctx} {A}> S.U B
  → Typed ctx S.U (S.pi A B)

macro "λcast" t:term:10 : term => `(cast (by lambda_solve) $t)

def castVar {ctx1 ctx2 ty1 ty2 tm1 tm2}
  (prog : Var ctx1 ty1 tm1)
  (h1 : ctx1 = ctx2)
  (h3 : ty1 = ty2)
  (h4 : tm1 = tm2)
  : Var ctx2 ty2 tm2 := by
  subst_vars
  exact prog

def castTyped {ctx1 ctx2 ty1 ty2 tm1 tm2}
  (prog : Typed ctx1 ty1 tm1)
  (h1 : ctx1 = ctx2)
  (h3 : ty1 = ty2)
  (h4 : tm1 = tm2)
  : Typed ctx2 ty2 tm2 := by
  subst_vars
  exact prog

macro "castVarM" t:term:10 : term => `(by eapply (castVar $t) <;> (lambda_solve <;> rfl))
macro "castTypedM" t:term:10 : term => `(by eapply (castTyped $t) <;> (lambda_solve <;> rfl))

example : Typed S.nil S.U S.U :=
  castTypedM (Typed.app (Typed.lambda (Typed.var Var.zero)) Typed.U)

-- (λ (T : U) (t : T). t) U U
-- example : Typed S.nil S.U S.U :=
--   castTypedM (Typed.app (castTypedM (Typed.app
--     (Typed.alambda Typed.U (Typed.alambda (Typed.var (castVarM Var.zero)) (Typed.var Var.zero)))
--     Typed.U)) Typed.U)

-- uh oh, may need SP. lets see:

example : Typed S.nil S.U S.U := by
  eapply
    (castTyped (Typed.app (castTyped (Typed.app
    (Typed.alambda Typed.U (Typed.alambda (Typed.var (castVar Var.zero ?a ?b ?c)) (Typed.var Var.zero)))
    Typed.U) ?d ?e ?f) Typed.U) ?g ?h ?i) <;> try (lambda_solve <;> rfl)

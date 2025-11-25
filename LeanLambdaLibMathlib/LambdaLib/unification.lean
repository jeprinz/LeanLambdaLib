import Mathlib.Tactic.failIfNoProgress -- why is this not in lean's standard library?

import LambdaLib.qterm
import LambdaLib.unificationFacts

open QuotTerm

/-
in this file, i'll define the actual unification tactic
-/

macro "lambda_solve" : tactic => `(tactic|
  repeat ( first
    | simp [lift_app, lift_lam, lift_var, lift_const, subst_app, subst_lam, subst_var,
      liftLiftMulti, substLiftMulti, subst_const, liftMultiZero, beta,
      lam_body_rw, const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2] at *
    | simp (disch := repeat constructor) [app_fact_rw, app_ne_const_rw, app_ne_var_rw] at *
    | fail_if_no_progress subst_vars -- TODO: maybe only have this go on equations of type QTerm
  )
)

-- for example, we want this to work:
example (t1 t2 : QTerm)
  (H : < (λ x. x) {t1} > = <λ x. x>)
  : <{t1} {t2}> = t2 := by
  lambda_solve

example (H : <λ x. A> = <λ x. B>) : False := by
  lambda_solve

example (H : <λ x. A> = <λ x. x>) : False := by
  lambda_solve

/-
there are two more cases i need unification to solve
1) deriving contradiction from applications with different var or consts on left being equal
x t1 = y t2 -> False,     A t1 = B t2 t3 -> False,  A t1 = x t2 -> False, .....
2) equality of children of application from equality of applications with same head and arity
x t1 t2 = y t1' t2' -> t1 = t1', t2 = t2'

see https://leanprover-community.github.io/extras/simp.html
simp can discharge premises to decide. maybe i can make eta reduce by making the lift property
decidable?

the idea would be make a property (incompatible : QTerm -> QTerm -> Prop) which holds when the terms
are apps with different l.h.s. or arities, and then
a theorem ((incompat t1 t2) → (t1 = t2) = False)
then it can simp by that

see: https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/#decidable-propositions
-/

#check app_ne_var
#check app_ne_const
#check app_fact

-- so i need to make simp able to try to prove QNeutral using (repeat constructor) maybe?

example (t1 t2 : QTerm) (H : <A {t1} > = <A {t2} >) : t1 = t2 := by
  lambda_solve

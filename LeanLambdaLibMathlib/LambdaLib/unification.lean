-- import Mathlib.Tactic.failIfNoProgress -- why is this not in lean's standard library?

import LambdaLib.qterm
import LambdaLib.unificationFacts
import Mathlib.Tactic

open QuotTerm

/-
in this file, i'll define the actual unification tactic
TODO: make an inductive predicate for z-free (generalize to nth-var-free), and use it
as an assumption for eta rule as well as a
zfree t1 → (t1 x = t2) = (t1 = λ x. t2)  rewrite rule.
this will work with the repeat constructor dispatch.
-/

macro "normalize" : tactic => `(tactic|
  simp only [lift_app, lift_lam, lift_var, lift_const,
      subst_app, subst_lam, subst_var, subst_const,
      liftLiftMulti, substLiftMulti, liftMultiZero,
      liftMulti_lam_rw, liftMulti_app_rw, liftMulti_var_rw, liftMulti_const_rw,
      beta] at *
)

macro "lambda_solve" : tactic => `(tactic|
  repeat ( first
    | simp at * -- TODO: figure out which lemmas this is using (relating to ∧) and write explicitly
    | normalize
    | simp only [lam_body_rw, const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2] at *
    | simp (disch := repeat constructor) only [app_fact_rw, app_ne_const_rw, app_ne_var_rw] at *
    | fail_if_no_progress subst_vars -- TODO: maybe only have this go on equations of type QTerm
    | casesm* _ ∧ _
    | casesm* QTerm × QTerm
    | simp [*] -- TODO: maybe i can use the `contextual' flag instead
  )
)

example (t1 t2 : QTerm)
  (H : < (λ x. x) {t1} > = <λ x. x>)
  : <{t1} {t2}> = t2 := by
  lambda_solve

example (H : <λ x. A> = <λ x. B>) : False := by
  lambda_solve

example (H : <λ x. A> = <λ x. x>) : False := by
  lambda_solve

example (t1 t2 : QTerm) (H : <A {t1} > = <A {t2} >) : t1 = t2 := by
  lambda_solve

example (H : <A B> = <A C>) : False := by
  lambda_solve

example (H : <A> = <B C>) : False := by
  lambda_solve

abbrev zero := <λ s z. z>
abbrev succ := <λ n. λ s z. s (n s z)>
abbrev plus := <λ a b. a {succ} (b {succ} {zero})>
abbrev mult := <λ a b. a (b {succ}) {zero}>

abbrev one := <{succ} {zero}>
abbrev two := <{succ} ({succ} {zero})>
abbrev four := <{succ} ({succ} {two})>


example : <{plus} {zero} {zero}> = zero := by
  lambda_solve

example : <{plus} {one} {one}> = two := by
  unfold plus one two succ zero
  lambda_solve

example : <{plus} {two} {two}> = four := by
  unfold plus two succ zero four
  lambda_solve

-- NOTE: it seems like abbrevs are more useful if they are not nested,
-- otherwise some unfolds are necessary anyway
abbrev two2 := <λ s z. s (s z)>
abbrev four2 := <λ s z. s (s (s (s z)))>
example : <{plus} {two2} {two2}> = four2 := by
  lambda_solve
  --

example : <{mult} {zero} {zero}> = zero := by
  lambda_solve

example : <{mult} {one} {one}> = one := by
  unfold mult succ one
  lambda_solve
  --

example : <{mult} {two} {two}> = four := by
  unfold two four mult succ zero
  lambda_solve
  --

-- TODO: consider removing liftMultiZero? it shouldn't always go.
example : <λ x. {plus} {zero} {zero}> = <λ x. {zero}> := by
  lambda_solve
  --

/-
note that we don't need a rule that combines two nested liftMultis.
this is because either there is a lambda between them, in which case
one of the liftMulti_*_rw rules eliminates the outer one,
or there isn't, in which case the liftMultiZero rule eliminates the inner one.
-/

example (t1 t2 : QTerm)
  (H : <A B C> = <A {t1} {t2} >)
  : <Res {t1} {t2}> = <Res B C> := by
  lambda_solve

example (t : Prod QTerm QTerm)
  (H : <A B C> = <A {t.1} {t.2} >)
  : <Res {t.1} {t.2}> = <Res B C> := by
  lambda_solve

example (t : Prod QTerm QTerm)
  (H : <A B C> = <A {t.1} {t.2} >)
  : t = ⟨<B>, <C>⟩ := by
  lambda_solve

-- TODO: make this not bad (if this works, then i can get rid of
-- Pmatch2 and just do Pmatch with a product type)
example (t1 t2 : QTerm × QTerm)
  (H1 : <A B C> = <A {t1.1} {t1.2} >)
  (H2 : <A B C> = <A {t2.1} {t2.2} >)
  : t1 = t2 := by
  lambda_solve

-- TODO: make this work better
example (t1 t2 t1' t2' : QTerm)
  (H1 : <A B C> = <A {t1} {t2} >)
  (H2 : <A B C> = <A {t1'} {t2'} >)
  : t1 = t1' := by
  lambda_solve

-- useful list of all mathlib tactics
-- https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md

-- example (A t1 t2 : QTerm)
--   (H : A = <A {t1} {t2} >)
--   : <Res {t1} {t2}> = <Res B C> := by
--   lambda_solve
--   --

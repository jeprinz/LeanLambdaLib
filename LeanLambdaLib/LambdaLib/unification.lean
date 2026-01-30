import Qq
import Lean


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

-- TODO: is there an idiomatic way to do the dispatches with typeclasses instead?

macro "normalize" : tactic => `(tactic|
  simp only [
    lift_app, lift_lam, lift_var, lift_const,
    subst_app, subst_lam, subst_var, subst_const,
    liftLiftMulti, substLiftMulti, liftMultiZero,
    liftMulti_lam_rw, liftMulti_app_rw, liftMulti_var_rw, liftMulti_const_rw,
    liftMultiLiftMulti,
    liftZeroToLiftMulti, -- is this good?
    beta,
    --
    substMulti, substMultiConst, substMultiEmpty, substMultiApp, substMultiLam,
    substMultiVar_rw, -- substMulti new ones
    -- eta_contract,
    --
    --
    Nat.one_lt_ofNat,   zero_lt_one, tsub_self, one_ne_zero,
    Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Nat.not_ofNat_lt_one, ↓reduceIte,
    Nat.reduceBEq, Bool.false_eq_true, lt_self_iff_false, BEq.rfl, ge_iff_le,
    nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, not_lt_zero', Nat.not_ofNat_le_one,
    Nat.reduceLeDiff, Nat.reduceLT, zero_le, Nat.pred_eq_sub_one, Nat.add_one_sub_one
  ] at *
    -- | simp (disch := repeat constructor) only [eta_contract] at *
)

open Lean hiding Term
open Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

-- partial def is_pattern (e : Expr) : MetaM Bool := do
  -- return true

abbrev val_to_sub (fresh_mv : QTerm) : QTerm :=
  <λ p. {fresh_mv} (p (λ x y. x)) (p (λ x y. y))>

elab "do_pair_case" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    -- let goalDecl ← goal.getDecl
    -- let goalType := goalDecl.type
    let goalType ← Lean.Elab.Tactic.getMainTarget
    -- should match on the goal to check that its in the right form with a metavar in the
    -- right place, and if so substitute it (either directly or by applying that theorem)
    -- or if not, it should fail so that the repeat its in knows that its done.
    match goalType with
    -- TODO: i should probably support the opposite ordering here as well
    | Expr.app (Expr.app (Expr.app (Expr.const `Eq _) _)
        (Expr.app (Expr.app (Expr.const `QuotTerm.app _)
          (Expr.app (Expr.app (Expr.const `QuotTerm.liftMulti _) _) (Expr.mvar mvid)))
          (Expr.app (Expr.app (Expr.const `QuotTerm.lam _) _)
            (Expr.app (Expr.app (Expr.const `QuotTerm.app _)
              (Expr.app (Expr.app (Expr.const `QuotTerm.app _ ) _p) _a)) _b))))
        _ =>
      let fresh_mv ← mkFreshExprMVar (Expr.const ``QTerm []) (userName := `fresh_mv)
      mvid.assign (Expr.app (Expr.const `val_to_sub []) fresh_mv)
    | _ =>
      throwTacticEx `do_pair_case goal "errro message"

macro "lambda_solve" : tactic => `(tactic|
  repeat ( first
    | fail_if_no_progress subst_vars -- TODO: maybe only have this go on equations of type QTerm
    | casesm* _ ∧ _
    | casesm* QTerm × QTerm
    | simp only [*, and_self, and_true, true_and,
      and_false, false_and] -- TODO: maybe i can use the `contextual' flag instead
    | simp (disch := (repeat' constructor) <;> grind only) only
      [eta_contract] at *
      -- [eta_contract, special_case_rw] at *
    | normalize
    | simp only [
      lam_body_rw, -- i checked, apparently this one is not needed in the canonicity proof
      const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2,
      SynTerm.Constant.strConst.injEq, String.reduceEq] at *
    | simp (disch := repeat constructor) only [app_fact_rw, app_ne_const_rw, app_ne_var_rw,
      app_ne_const_rw2, app_ne_var_rw2] at *
    | do_pair_case
    | apply Eq.symm; do_pair_case
    -- NOTE: these next two lines should be redundant to the call with simp above IF LEAN
    -- WASN'T STUPID. however, disch doesn't work when the goal being dispatched to
    -- has metavariables in it.
    | (rw [special_case_rw] at *
      ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)) <;> [skip]
    | (apply Eq.symm; rw [special_case_rw] at *
      ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)) <;> [skip]
    -- again, this should be redundant except for the bug with disch and metavars
    | (rw [app_fact_rw] at *
      ; (iterate 2 on_goal 2 => ((repeat constructor) <;> fail))) <;> [skip]
  )
)

example (t1 t2 : QTerm)
  (H : < (λ x. x) {t1} > = <λ x. x>)
  : <{t1} {t2}> = t2 := by
  lambda_solve
  --

example (H : <λ x. A> = <λ x. B>) : False := by
  lambda_solve

example (H : <λ x. A> = <λ x. x>) : False := by
  lambda_solve

example (t1 t2 : QTerm) (H : <A {t1} > = <A {t2} >) : t1 = t2 := by
  lambda_solve
  --

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
  --

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

example (B C : QTerm) (H : <(λ x y z. A x y z) {B} D E> = <(λ x y z . A x y z) {C} D E>)
  : B = C := by
  lambda_solve

example (I C : QTerm)
  (H : <(λ x y z. A x y z) {I} D E> = <(λ x y z . A x y z) (λ x. x) D E>)
  (H2 : <{I} C> = <Result>)
  : C = <Result> := by
  lambda_solve

-- eta expansion
example : <λ x . A x> = <A> := by
  lambda_solve

example : <λ x y . A x y> = <A> := by
  lambda_solve

example : <λ x y z . A x y z> = <A> := by
  lambda_solve

example : <λ x y z w . A x y z w> = <A> := by
  lambda_solve

example (t : QTerm) : <λ x . {t} x> = t := by
  lambda_solve

-- demonstration of a problem with simp and indexed types:
-- inductive IndexedType : QTerm → Type where
-- inductive IndexedProp : QTerm → Prop where
--
-- example
--   (H1 : IndexedType <(λ x . x) A>)
--   (H2 : IndexedProp <(λ x . x) A>)
--    : IndexedType <A> × Inhabited (IndexedProp <A>):= by
--   lambda_solve
--   sorry
--   -- simp only [beta] at *
--   -- for some crazy reason, this doesn't work when its a Type.
--   --

-- TODO: why does my notation mechanism make x be var 0? shouldn't it raise an error?
-- example (t : QTerm) (H : < {liftMulti 1 t} x> = <x>) : t = <λ x. x> := by
  -- lambda_solve

-- example (t : QTerm) (H : < {liftMulti 2 t} {var 0} {var 1} > = <A {var 0} {var 1} >)
  -- : t = <λ x y. A x y> := by
  -- lambda_solve

-- example (t : QTerm) (H : < {liftMulti 2 t} {var 1} {var 0} > = <A {var 1} {var 0} >)
  -- : t = <λ x y. A x y> := by
  -- lambda_solve
  --

-- example a b c
--   : ∃ mv, <{liftMulti 1 mv} (λ p. p {a} {b})> = c := by
--   refine (Exists.intro ?_ ?_)
--   rotate_left
--   · --
--     -- this is where i can check that my elaborator matches
--     -- apply pair_specialize_case_test
--     do_pair_case
--     normalize
--     lambda_solve
--     -- simp (disch := (repeat' constructor) <;> try grind only) only [special_case_rw] at *
--     rw [special_case_rw]
--     --
--     sorry

-- example (t : QTerm) (H : < {liftMulti 1 t} (λ p. p x y)> = <x>)
--   : t = <λ p. p (λ x y. x)> := by
--   lambda_solve
--   --
--   sorry

-- useful list of all mathlib tactics
-- https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md

-- example (A t1 t2 : QTerm)
--   (H : A = <A {t1} {t2} >)
--   : <Res {t1} {t2}> = <Res B C> := by
--   lambda_solve
--   --

-- https://github.com/tristan-f-r/mathlib4-tactics

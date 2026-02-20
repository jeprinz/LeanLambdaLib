import Lean


import LambdaLib.qterm
import LambdaLib.unificationFacts
-- import Mathlib.Tactic.failIfNoProgress
-- import Mathlib.Tactic.CasesM
-- import Mathlib.Tactic
import Mathlib.Tactic.CasesM
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.NeZero
import Init.Data.Nat.Basic
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
import Mathlib.Algebra.Order.GroupWithZero.Canonical

open QuotTerm

/-
the higher order unification tactic
it mostly rerwites by theorems from unificationFacts.lean.
there are also some other cases needed.
-/

macro "normalize" : tactic => `(tactic|
  simp only [
    lift_app, lift_lam, lift_var, lift_const,
    subst_app, subst_lam, subst_var, subst_const,
    liftLiftMulti, substLiftMulti, liftMultiZero,
    liftMulti_lam_rw, liftMulti_app_rw, liftMulti_var_rw, liftMulti_const_rw,
    liftMultiLiftMulti,
    liftZeroToLiftMulti,
    beta,
    --
    substMulti, substMultiConst, substMultiEmpty, substMultiApp, substMultiLam,
    substMultiVar_rw,
    --
    --
    Nat.one_lt_ofNat,   zero_lt_one, tsub_self, one_ne_zero,
    Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Nat.not_ofNat_lt_one, ↓reduceIte,
    Nat.reduceBEq, Bool.false_eq_true, lt_self_iff_false, BEq.rfl, ge_iff_le,
    nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, not_lt_zero', Nat.not_ofNat_le_one,
    Nat.reduceLeDiff, Nat.reduceLT, zero_le, Nat.pred_eq_sub_one, Nat.add_one_sub_one
  ] at *
)

open Lean hiding Term
open Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

partial def is_pattern (e : Expr) (seenpair : Bool) : MetaM Bool := do
  match e with
  | Expr.app (Expr.app (Expr.const `QuotTerm.lam _) _)
      (Expr.app (Expr.app (Expr.const `QuotTerm.app _)
      (Expr.app (Expr.app (Expr.const `QuotTerm.app _ )
      -- TODO: should check that the zero is actually index zero instead of just calling it zero
      (Expr.app (Expr.const `QuotTerm.var _) _zero)) a)) b)
    => do let x <- is_pattern a true
          let y <- is_pattern b true
          return x && y
  -- ideally should also check that indices are unique
  | Expr.app (Expr.const `QuotTerm.var _) _index => return seenpair
  | _ => return false

abbrev val_to_sub (fresh_mv : QTerm) : QTerm :=
  <λ p. {fresh_mv} (p (λ x y. x)) (p (λ x y. y))>

elab "do_pair_case" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    match goalType with
    | Expr.app (Expr.app (Expr.app (Expr.const `Eq _) _)
        (Expr.app (Expr.app (Expr.const `QuotTerm.app _)
          (Expr.app (Expr.app (Expr.const `QuotTerm.liftMulti _) _) (Expr.mvar mvid)))
          pattern))
        _ =>
      let isgood <- is_pattern pattern false
      if isgood then
        let fresh_mv ← mkFreshExprMVar (Expr.const ``QTerm []) (userName := `fresh_mv)
        mvid.assign (Expr.app (Expr.const `val_to_sub []) fresh_mv)
      else throwTacticEx `do_pair_case goal "pattern was not right"
    | _ =>
      throwTacticEx `do_pair_case goal "errro message"

macro "lambda_solve" : tactic => `(tactic|
  repeat ( first
    | fail_if_no_progress subst_vars -- ideally should only go on equations of type QTerm
    | casesm* _ ∧ _
    | casesm* QTerm × QTerm
    | simp only [*, and_self, and_true, true_and,
      and_false, false_and]
    | simp (disch := (repeat' constructor) <;> grind only) only
      [eta_contract] at *
    | normalize
    | simp only [
      lam_body_rw, -- i checked, apparently this one is not needed in the canonicity proof
      const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2,
      SynTerm.Constant.strConst.injEq, String.reduceEq] at *
    | simp (disch := repeat constructor) only [app_fact_rw, app_ne_const_rw, app_ne_var_rw,
      app_ne_const_rw2, app_ne_var_rw2] at *
    | do_pair_case
    | apply Eq.symm; do_pair_case
    -- NOTE: these next three cases should be redundant to the call with simp above if simp
    -- worked the way it should. however, disch doesn't work when the goal being dispatched to
    -- has metavariables in it.
    | (rw [special_case_rw] at *
      ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)) <;> [skip]
    | (apply Eq.symm; rw [special_case_rw] at *
      ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)) <;> [skip]
    | (rw [app_fact_rw] at *
      ; (iterate 2 on_goal 2 => ((repeat constructor) <;> fail))) <;> [skip]
  )
)

import LambdaLib.qterm

open QuotTerm

/-
in this file, i'll define the actual unification tactic
-/

theorem lam_body_rw {t1 t2 s1 s2} : (lam s1 t1 = lam s2 t2) = (t1 = t2) := by
  apply propext
  apply Iff.intro
  · apply lam_body
  · intros
    subst_vars
    exact alpha

theorem const_inj_rw {c1 c2} : (const c1 = const c2) = (c1 = c2) := by
  apply propext
  apply Iff.intro
  · apply const_inj
  · intros; subst_vars; rfl

theorem var_inj_rw {i1 i2} : (var i1 = var i2) = (i1 = i2) := by
  apply propext
  apply Iff.intro
  · apply var_inj
  · intros; subst_vars; rfl

-- TODO: i think this and the next theorem will be redundant with the general neutral form cases?
theorem var_not_const_rw {i c} : (var i = const c) = False := by
  apply propext
  apply Iff.intro
  · apply var_not_const
  · intros; contradiction

theorem var_not_const_rw2 {i c} : (const c = var i) = False := by
  rw (config := {occs := .pos [2]}) [propext (Iff.intro Eq.symm Eq.symm)]
  apply var_not_const_rw

macro "basic_lambda_solve" : tactic => `(tactic|
  repeat ( first
    | simp [lift_app, lift_lam, lift_var, lift_const, subst_app, subst_lam, subst_var,
      liftLiftMulti, substLiftMulti, subst_const, liftMultiZero, beta,
      lam_body_rw, const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2] at *
    | subst_vars -- TODO: maybe only have this go on equations of type QTerm
  )
)

-- for example, we want this to work:
example (t1 t2 : QTerm)
  (H : < (λ x. x) {t1} > = <λ x. x>)
  : <{t1} {t2}> = t2 := by
  basic_lambda_solve

example (H : <λ x. A> = <λ x. B>) : False := by
  basic_lambda_solve

example (H : <λ x. A> = <λ x. x>) : False := by
  basic_lambda_solve

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

inductive Lhs : Type where
| var : Nat → Lhs
| const : SynTerm.Constant → Lhs

open SynTerm

inductive NeutralWithArity : Lhs → Nat → Term → Prop where
| const : ∀{c}, NeutralWithArity (Lhs.const c) 0 (Term.const c)
| var : ∀{n}, NeutralWithArity (Lhs.var n) 0 (Term.var n)
| app : ∀{lhs t a arg}, NeutralWithArity lhs a t
  → NeutralWithArity lhs (Nat.succ a) (Term.app t arg)

theorem stepNeutral {lhs a t1 t2} (step : (union Step StepEta) t1 t2)
  (H : NeutralWithArity lhs a t1)
  : NeutralWithArity lhs a t2 := by
  cases step with
  | r step => cases step with
    | app1 step =>
      cases H
      constructor
      apply (stepNeutral (union.r step))
      assumption
    | app2 _ =>
      cases H
      constructor
      assumption
    | beta =>
      cases H with | app H => _
      cases H
    | lam _ => cases H
  | s step => cases step with
    | app1 step =>
      cases H
      constructor
      apply (stepNeutral (union.s step))
      assumption
    | app2 _ =>
      cases H
      constructor
      assumption
    | _ => cases H

theorem allstepNeutral {lhs a t1 t2} (step : AllStep t1 t2)
  (H : NeutralWithArity lhs a t1)
  : NeutralWithArity lhs a t2 := by
  induction step with
  | refl => assumption
  | cons _ _ ih =>
    apply ih
    apply stepNeutral <;> assumption

inductive QNeutralWithArity : Lhs → Nat → QTerm → Prop where
| const : ∀{c}, QNeutralWithArity (Lhs.const c) 0 (const c)
| var : ∀{n}, QNeutralWithArity (Lhs.var n) 0 (var n)
| app : ∀{lhs t a arg}, QNeutralWithArity lhs a t → QNeutralWithArity lhs (Nat.succ a) (app t arg)

theorem liftNeutralWithArity {lhs a t}
  : NeutralWithArity lhs a t ↔ QNeutralWithArity lhs a (Quotient.mk _ t) := by
  apply Iff.intro
  ·
    intro H
    induction H with
    | const =>
      apply QNeutralWithArity.const
      --
      sorry
    | var => sorry
    | app _ _ => sorry
    --
    sorry
  · sorry

-- i need a theorem that says that 2 neutrals of different arities are unequal?
-- or maybe prove this first on SynTerm.Terms?
theorem nwa_inj {t} {lhs1 lhs2} {a1 a2}
  (H1 : QNeutralWithArity lhs1 a1 t)
  (H2 : QNeutralWithArity lhs2 a2 t)
  : a1 = a2 ∧ lhs1 = lhs2 := by
  induction H1 with -- try simp
  | @const c =>
    --
    generalize bla : (const c) = thing at *
    cases H2
    --
    sorry
  | var =>
    --
    sorry
  | app _ _ =>
    --
    sorry
  --
  --
  --

theorem neutral_unequal {t1 t2} {lhs1 lhs2} {a1 a2}
  (H1 : QNeutralWithArity lhs1 a1 t1)
  (H2 : QNeutralWithArity lhs2 a2 t2)
  (notsame : a1 ≠ a2 ∨ lhs1 ≠ lhs2)
  : t1 ≠ t2 := by
  --
  --
  --
  sorry

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

open SynTerm

inductive Neutral : Term → Prop where
| const : ∀{c}, Neutral (Term.const c)
| var : ∀{n}, Neutral (Term.var n)
| app : ∀{t arg}, Neutral t → Neutral (Term.app t arg)

theorem stepNeutral {t1 t2} (step : (union Step StepEta) t1 t2)
  (H : Neutral t1)
  : Neutral t2 := by
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

theorem allstepNeutral {t1 t2} (step : AllStep t1 t2)
  (H : Neutral t1)
  : Neutral t2 := by
  induction step with
  | refl => assumption
  | cons _ _ ih =>
    apply ih
    apply stepNeutral <;> assumption

lemma appStep' {a b t} (step : (union Step StepEta) (Term.app a b) t) (neut : Neutral a)
  : ∃ a' b', t = Term.app a' b' ∧ Neutral a' := by
  cases step with | r step => _ | s step => _ <;> cases step <;> (try (cases neut; done))
    <;> try grind
  · refine ⟨_, _, rfl, ?_⟩
    apply (stepNeutral _ neut)
    apply union.r
    assumption
  · refine ⟨_, _, rfl, ?_⟩
    apply (stepNeutral _ neut)
    apply union.s
    assumption

theorem appStep {a b t} (step : AllStep (Term.app a b) t) (neut : Neutral a)
  : ∃ a' b', t = Term.app a' b' := by
  generalize eqn : (Term.app a b) = t1 at *
  induction step generalizing a b with
  | refl => grind
  | cons s ss ih =>
    subst_vars
    have ⟨a', b', eq, neut'⟩ := appStep' s neut
    subst_vars
    apply (ih neut' rfl)

inductive QNeutral : QTerm → Prop where
| const : ∀{c}, QNeutral (const c)
| var : ∀{n}, QNeutral (var n)
| app : ∀{t arg}, QNeutral t → QNeutral (app t arg)

theorem liftNeutralWithArity {t}
  : Neutral t → QNeutral (Quotient.mk _ t) := by
  intro H
  induction H with
  | @const c =>
    have thing := @QNeutral.const c
    unfold const at thing
    assumption
  | @var i =>
    have thing := @QNeutral.var i
    unfold var at thing
    assumption
  | @app a b qn =>
    -- apply Quotient.ind _ a
    have thing := @QNeutral.app ⟦a⟧ ⟦b⟧
    simp [app] at thing
    apply thing
    assumption

theorem lowerNeutralWithArity {q} (H : QNeutral q)
  : ∃ t, ⟦t⟧ = q ∧ Neutral t := by
  induction H with
  | @const c =>
    exists .const c
    simp [const]
    repeat' constructor
  | @var i =>
    exists .var i
    simp [var]
    repeat' constructor
  | @app a b qn ih =>
    rcases ih with ⟨t, rfl, neu⟩
    apply Quotient.ind _ b
    intro b
    exists .app t b
    simp [app]
    constructor
    assumption

-- i would need these three theorems to make the unification tactic work
theorem app_ne_var {i a b} (qneut : QNeutral a) (eq : var i = app a b) : False := by
  have ⟨t, eq2, neut⟩ := lowerNeutralWithArity qneut
  subst_vars
  revert eq
  apply Quotient.ind _ b
  intro b eq
  simp [var, app] at eq
  have ⟨t', l, r⟩ := Quotient.exact eq
  rcases varStep l with rfl
  rcases appStep r neut with ⟨_, _, eq⟩
  cases eq

theorem app_ne_const {c a b} (qneut : QNeutral a) (eq : const c = app a b) : False := by
  have ⟨t, eq2, neut⟩ := lowerNeutralWithArity qneut
  subst_vars
  revert eq
  apply Quotient.ind _ b
  intro b eq
  simp [const, app] at eq
  have ⟨t', l, r⟩ := Quotient.exact eq
  rcases constStep l with rfl
  rcases appStep r neut with ⟨_, _, eq⟩
  cases eq

theorem app_fact {a b a' b'} (qneut : QNeutral a) (qneut' : QNeutral a')
  (eq : app a b = app a' b') : a = a' /\ b = b' := by
  have ⟨t, eq2, neut⟩ := lowerNeutralWithArity qneut
  have ⟨t, eq2, neut'⟩ := lowerNeutralWithArity qneut'
  subst_vars
  revert eq
  apply Quotient.ind _ b
  apply Quotient.ind _ b'
  intro b b' eq
  simp [app] at eq
  have ⟨t', l, r⟩ := Quotient.exact eq
  rcases appStep l neut with ⟨_, _, eq⟩
  rcases appStep r neut' with ⟨_, _, eq⟩
  subst_vars
  --
  sorry

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

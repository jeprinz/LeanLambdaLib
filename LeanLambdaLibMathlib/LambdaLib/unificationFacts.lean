import LambdaLib.qterm

open QuotTerm

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

theorem var_not_const_rw {i c} : (var i = const c) = False := by
  apply propext
  apply Iff.intro
  · apply var_not_const
  · intros; contradiction

theorem var_not_const_rw2 {i c} : (const c = var i) = False := by
  rw (config := {occs := .pos [2]}) [propext (Iff.intro Eq.symm Eq.symm)]
  apply var_not_const_rw

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

def SmallStep := closeRef (union Step StepEta)

lemma appStep' {a b t} (step : (union Step StepEta) (Term.app a b) t) (neut : Neutral a)
  : ∃ a' b', t = Term.app a' b' ∧ SmallStep a a' ∧ SmallStep b b' /-Neutral a'-/ := by
  cases step with | r step => _ | s step => _ <;> cases step <;> (try (cases neut; done))
  · refine ⟨_, _, rfl, ?_⟩
    apply And.intro
    · apply Or.inr
      apply union.r
      assumption
    · apply Or.inl
      rfl
  · refine ⟨_, _, rfl, ?_⟩
    apply And.intro
    · apply Or.inl
      rfl
    · apply Or.inr
      apply union.r
      assumption
  · refine ⟨_, _, rfl, ?_⟩
    apply And.intro
    · apply Or.inr
      apply union.s
      assumption
    · apply Or.inl
      rfl
  · refine ⟨_, _, rfl, ?_⟩
    apply And.intro
    · apply Or.inl
      rfl
    · apply Or.inr
      apply union.s
      assumption

theorem appStep {a b t} (step : AllStep (Term.app a b) t) (neut : Neutral a)
  : ∃ a' b', t = Term.app a' b' ∧ AllStep a a' ∧ AllStep b b' := by
  generalize eqn : (Term.app a b) = t1 at *
  induction step generalizing a b with
  | refl =>
    subst_vars
    exists a, b
    exact ⟨rfl, closure.refl, closure.refl⟩
  | cons s ss ih =>
    subst_vars
    have ⟨a', b', eq, stepa, stepb⟩ := appStep' s neut
    have neut' := allstepNeutral (closeRefToClosure stepa) neut
    subst_vars
    -- have test := (ih neut' rfl)
    have ⟨ a'', b'', eq, ssa, ssb⟩  := ih neut' rfl
    subst_vars
    exists a'', b''
    apply And.intro
    · rfl
    · apply And.intro
      · exact (transitivity (closeRefToClosure stepa) ssa)
      · exact (transitivity (closeRefToClosure stepb) ssb)

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
  rcases eq with ⟨eq, _, _⟩
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
  rcases eq with ⟨eq, _, _⟩
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
  rcases appStep l neut with ⟨_, _, eq, x, y⟩
  rcases appStep r neut' with ⟨_, _, eq, z, w⟩
  subst_vars
  cases eq
  apply And.intro <;> apply Quotient.sound
  · refine ⟨_, x, z⟩
  · refine ⟨_, y, w⟩

theorem app_ne_var_rw {i a b} (qneut : QNeutral a) : (var i = app a b) = False := by
  apply propext
  apply Iff.intro
  · apply app_ne_var qneut
  · intros
    contradiction

theorem app_ne_var_rw2 {i a b} (qneut : QNeutral a) : (app a b = var i) = False := by
  rw (config := {occs := .pos [2]}) [propext (Iff.intro Eq.symm Eq.symm)]
  apply app_ne_var_rw
  assumption

theorem app_ne_const_rw {c a b} (qneut : QNeutral a) : (const c = app a b) = False := by
  apply propext
  apply Iff.intro
  · apply app_ne_const qneut
  · intros
    contradiction

theorem app_ne_const_rw2 {c a b} (qneut : QNeutral a) : (app a b = const c) = False := by
  rw (config := {occs := .pos [2]}) [propext (Iff.intro Eq.symm Eq.symm)]
  apply app_ne_const_rw
  assumption

theorem app_fact_rw {a b a' b'} (qneut : QNeutral a) (qneut' : QNeutral a')
  : (app a b = app a' b') = (a = a' /\ b = b') := by
  apply propext
  apply Iff.intro
  · apply app_fact qneut qneut'
  · intro ⟨eq1, eq2⟩
    subst_vars
    rfl

-- these are to replace liftMulti with lifts when it is around a lam, app, var, or const.
theorem liftMulti_lam_rw {s t i}
  : liftMulti (Nat.succ i) (lam s t) = lift 0 (liftMulti i (lam s t)) := by
  simp [QuotTerm.liftLiftMulti]
theorem liftMulti_app_rw {t1 t2 i}
  : liftMulti (Nat.succ i) (app t1 t2) = lift 0 (liftMulti i (app t1 t2)) := by
  simp [QuotTerm.liftLiftMulti]
theorem liftMulti_var_rw {i j}
  : liftMulti (Nat.succ i) (var j) = lift 0 (liftMulti i (var j)) := by
  simp [QuotTerm.liftLiftMulti]
theorem liftMulti_const_rw {c}
  : liftMulti (Nat.succ i) (const c) = lift 0 (liftMulti i (const c)) := by
  simp [QuotTerm.liftLiftMulti]

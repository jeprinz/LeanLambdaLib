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

theorem liftZeroToLiftMulti {t} : QuotTerm.lift 0 t = liftMulti 1 t := by
  apply Quotient.ind _ t
  intros
  simp [QuotTerm.liftMulti, QuotTerm.lift, SynTerm.liftMulti]

theorem liftMultiLiftMulti {n m} {t : QTerm}
  : liftMulti n (liftMulti m t) = liftMulti (n + m) t := by
  apply Quotient.ind _ t
  intros
  simp [QuotTerm.liftMulti]
  apply Quotient.sound
  simp [SynTerm.liftMultiLiftMulti]
  apply refl

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


-- describes terms that don't refer to the i'th variable
inductive iFree : Nat → QTerm → Prop where
| var : ∀ i j, i ≠ j → iFree i (var j)
| lam : ∀ s t i, iFree i.succ t → iFree i (lam s t)
| app : ∀ a b i, iFree i a → iFree i b → iFree i (app a b)
| const : ∀ c i, iFree i (const c)
| liftMulti : ∀ i j t, j > i → iFree i (liftMulti j t)
| lift : ∀ i t, iFree i (lift i t)

theorem iFreeLift {t i} (ifree : iFree i t)
  : ∃ t', t = QuotTerm.lift i t' := by
  induction ifree with
  | var i j _ =>
    exists (var (if i < j then j - 1 else j ))
    grind [lift_var]
  | lam s t i _ ih =>
    rcases ih with ⟨t', ih⟩
    exists (lam s t')
    grind [lift_lam]
  | app a b i _ _ iha ihb =>
    rcases iha with ⟨a', iha⟩
    rcases ihb with ⟨b', ihb⟩
    exists (app a' b')
    grind [lift_app]
  | const c i =>
    exists const c
    simp [lift_const]
  | liftMulti i j t =>
    have ⟨a, p⟩ : ∃ a, (i + a).succ = j := by
      exists (j - i - 1)
      grind
    exists (liftMulti i (liftMulti a t))
    rw [_root_.liftMultiLiftMulti]
    rw [QuotTerm.liftLiftMulti] <;> grind
  | lift i t => exists t

theorem eta_contract s t (H : iFree 0 t) : lam s (app t (var 0)) = subst 0 <Dummy> t := by
  have ⟨t', eq⟩ := iFreeLift H
  subst t
  simp [eta]
  rw [QuotTerm.subst_lift]

--------------------------------------

-- need to generalize this
theorem special_case_0 t1 t2 (ifree : iFree 0 t1) (H : app t1 (var 0) = t2)
  : subst 0 <Dummy> t1 = lam "x" t2 := by
  subst t2
  rw [eta_contract]
  assumption

theorem special_case i t1 t2 (ifree : iFree i t1) (H : app t1 (var i) = t2)
  : subst i <Dummy> t1 = lam "x" (subst i.succ (var 0) (lift 0 t2)) := by
  subst t2
  simp only [Nat.succ_eq_add_one, lift_app, lift_var, ge_iff_le, Nat.zero_le,
    ↓reduceIte, subst_app, subst_var, lt_self_iff_false, BEq.rfl]
  have fact : ∀ t, QuotTerm.lift 0 (QuotTerm.lift i t)
    = QuotTerm.lift i.succ (QuotTerm.lift 0 t) := by
    intros
    rw (occs := [2]) [QuotTerm.lift_lift] <;> simp
  rw [eta_contract]
  · rcases iFreeLift ifree with ⟨t1', rfl⟩
    rw [fact]
    clear fact
    repeat rw [QuotTerm.subst_lift]
  · rcases iFreeLift ifree with ⟨t1', rfl⟩
    rw [fact]
    clear fact
    repeat rw [QuotTerm.subst_lift]
    constructor

-- then the idea would be special_case_rw : (t1 x = t2) = (t1 = λ x. t2)
theorem special_case_rw i t1 t2 (ifree : iFree i t1)
  : (app t1 (var i) = t2) =
    (subst i <Dummy> t1 = lam "x" (subst i.succ (var 0) (lift 0 t2))) := by
  apply propext
  apply Iff.intro
  · apply special_case ; assumption
  · intros p
    rcases iFreeLift ifree with ⟨t1', rfl⟩
    clear ifree
    rw [QuotTerm.subst_lift] at p
    subst t1'
    simp only [lift_lam, beta]
    simp only [QuotTerm.lift_subst, lt_self_iff_false, ↓reduceIte, lift_var]
    simp [QuotTerm.lift_lift]
    simp [QuotTerm.subst_subst_2]
    simp [QuotTerm.subst_lift]
    simp [subst_var]
    rw [<- QuotTerm.subst_lift_2]

-- <(λ p. {x'} (p (λ x y. x)) (p (λ x y. y))) (λ p. p {a} {b})> = c
-- theorem pair_specialize_case
--   (x' a b c sp2 /-sp1 sx1 sy1 sx2 sy2-/ i)
--   (H :
--     app (liftMulti i <λ p. {x'} (p (λ x y. x)) (p (λ x y. y))>)
--     (lam sp2 (app (app (var 0) a) b))
--     = c)
--   : app (liftMulti i <λ p. {x'} (p (λ x y. x)) (p (λ x y. y))>)
--     (lam sp2 (app (app (var 0) a) b))
--     = c
--     := by assumption

--------------------------------------
-- TODO: probably delete this substMulti stuff later if i don't end up using it.

def substMulti (i : Nat) (ts : List QTerm) (t : QTerm) : QTerm :=
  match ts with
  | [] => t
  | t1 :: ts' => substMulti i ts' (subst i (liftMulti i t1) t)
  -- an alternate idea is to do the lifts on the ts in the substMultiLam rewrite?

theorem substMultiConst i ts c : substMulti i ts (const c) = const c := by
  induction ts with
  | nil => rfl
  | cons head tail ih =>
    simp [substMulti]
    rw [subst_const]
    assumption

theorem substMultiEmpty i t : substMulti i [] t = t := by rfl

theorem substMultiSubst i t1 t2 ts -- this one is not to be maximally rewritten indescriminately
  : substMulti i (t1 :: ts) t2 = substMulti i ts (subst i (liftMulti i t1) t2) := by rfl

theorem substMultiApp i ts t1 t2 : substMulti i ts (app t1 t2)
  = app (substMulti i ts t1) (substMulti i ts t2) := by
  induction ts generalizing t1 t2 with
  | nil => rfl
  | cons head tail ih =>
    simp [substMulti]
    rw [subst_app]
    rw [ih]

theorem substMultiLam i ts s t : substMulti i ts (lam s t) = lam s (substMulti i.succ ts t) := by
  induction ts generalizing t with
  | nil => rfl
  | cons head tail ih =>
    simp [substMulti]
    rw [subst_lam]
    rw [ih]
    rw [<- QuotTerm.liftLiftMulti]
    simp

theorem substMultiVar_rw i t1 x ts
  : substMulti i (t1 :: ts) (var x) = substMulti i ts (subst i (liftMulti i t1) (var x)) :=
  by apply substMultiSubst

-- theorem substSubstMulti env t t'
--   : (subst 0 t' (substMulti 1 env t)) = substMulti 0 env (subst 0 t' t) := by
--   induction env generalizing t with
--   | nil => rfl
--   | cons head tail ih =>
--     simp [substMulti]
--     rw [ih]
--     simp [<- QuotTerm.liftLiftMulti, liftMultiZero]
--     simp [QuotTerm.subst_subst]
--     --
--     sorry

-- theorem substSubstMulti env i t t'
--   : (subst i t' (substMulti i.succ env t)) = substMulti i env (subst i t' t) := by
--   induction env generalizing t with
--   | nil => rfl
--   | cons head tail ih =>
--     --
--     --
--     simp [substMulti]
--     rw [ih]
--     --
--     simp [QuotTerm.subst_subst]
--     --
--     simp [QuotTerm.substLiftMulti]
--     --

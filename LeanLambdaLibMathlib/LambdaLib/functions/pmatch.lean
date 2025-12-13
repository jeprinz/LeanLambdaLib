-- not sure what the standard way to do this in lean is, but here is a way:
-- TODO: its Classical.some_spec₂ from mathlib, see other file.
theorem choiceInd.{u} (T : Type u) (P Q : T → Prop) x
  (H : forall t, P t → Q t) : Q (@Classical.choose T P x) := by
  apply H
  apply Classical.choose_spec

noncomputable def Pmatch.{u1, u2} {T : Type u1} {A : Type u2} (P : T → Prop)
  (branch1 : T → A) (branch2 : A) : A := by
  refine (@Classical.choose _
    (fun a => (∃ t, P t ∧ branch1 t = a) ∨ ((¬ ∃ t, P t) ∧ a = branch2))
    ?_)
  cases Classical.em (∃ t, P t) with
  | inl p =>
    rcases p with ⟨t, pt⟩
    exists (branch1 t)
    apply Or.inl
    exists t
  | inr np =>
    exists branch2
    apply Or.inr
    trivial

theorem PmatchDef1.{u1,u2} {T : Type u1} {A : Type u2} {P : T → Prop} {t : T} (H : P t)
  (unique : forall t1 t2, P t1 → P t2 → t1 = t2)
  (branch1 : T → A) (branch2 : A)
  : Pmatch P branch1 branch2 = branch1 t := by
  unfold Pmatch
  apply choiceInd _ _ (fun x => x = branch1 t) _ _
  intros a c
  cases c <;> grind

theorem PmatchDef2 {T A : Type} (P : T → Prop)
  (branch1 : T → A) (branch2 : A)
  (ne : forall t, P t → False)
  : Pmatch P branch1 branch2 = branch2 := by
  unfold Pmatch
  apply choiceInd _ _ (fun x => x = branch2)
  intros a c
  cases c <;> grind

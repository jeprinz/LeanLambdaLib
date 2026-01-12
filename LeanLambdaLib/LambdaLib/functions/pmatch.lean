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
  apply choiceInd _ _ (fun x => x = branch1 t) _ _
  intros a c
  cases c <;> grind

theorem PmatchDef2.{u1, u2} {T : Type u1} {A : Type u2} (P : T → Prop)
  (branch1 : T → A) (branch2 : A)
  (ne : forall t, P t → False)
  : Pmatch P branch1 branch2 = branch2 := by
  unfold Pmatch
  apply choiceInd _ _ (fun x => x = branch2)
  intros a c
  cases c <;> grind

noncomputable def Pmatch2.{u1, u2} {T1 T2 : Type u1} {A : Type u2} (P : T1 → T2 → Prop)
  (branch1 : T1 → T2 → A) (branch2 : A) : A :=
  @Pmatch (Prod T1 T2) _ (fun t ↦ P t.1 t.2) (fun t ↦ branch1 t.1 t.2) branch2

theorem Pmatch2Def1.{u1,u2} {T1 T2 : Type u1} {A : Type u2} {P : T1 → T2 → Prop}
  {t1 : T1} {t2 : T2} (H : P t1 t2)
  (unique1 : forall t1 t2 t1' t2', P t1 t2 → P t1' t2' → t1 = t1')
  (unique2 : forall t1 t2 t1' t2', P t1 t2 → P t1' t2' → t2 = t2')
  (branch1 : T1 → T2 → A) (branch2 : A)
  : Pmatch2 P branch1 branch2 = branch1 t1 t2 := by
  apply choiceInd _ _ (fun x => x = branch1 t1 t2)
  intros a c
  cases c <;> simp at * <;> grind

theorem Pmatch2Def2.{u1, u2} {T1 T2 : Type u1} {A : Type u2} (P : T1 → T2 → Prop)
  (branch1 : T1 → T2 → A) (branch2 : A)
  (ne : forall t1 t2, P t1 t2 → False)
  : Pmatch2 P branch1 branch2 = branch2 := by
  apply choiceInd _ _ (fun x => x = branch2)
  intros a c
  cases c <;> grind

noncomputable def Pmatch3.{u1, u2} {T1 T2 T3 : Type u1} {A : Type u2} (P : T1 → T2 → T3 → Prop)
  (branch1 : T1 → T2 → T3 → A) (branch2 : A) : A :=
  @Pmatch (T1 × T2 × T3) _
    (fun t ↦ P t.1 t.2.1 t.2.2) (fun t ↦ branch1 t.1 t.2.1 t.2.2) branch2

noncomputable def Pif.{u} {A : Type u} (P : Prop)
  (branch1 : A) (branch2 : A) : A :=
  @Pmatch Unit _ (fun _ ↦ P) (fun _ ↦ branch1) branch2

theorem PifDef1.{u} {A : Type u} {P : Prop} (H : P)
  (branch1 branch2 : A)
  : Pif P branch1 branch2 = branch1 := by
  apply choiceInd _ _ (fun x => x = branch1) _ _
  intros a c
  cases c with
  | inl _ => grind
  | inr p =>
    rcases p with ⟨p, _⟩
    exfalso
    apply p
    exists .unit

theorem PifDef2.{u} {A : Type u} {P : Prop} (H : ¬ P)
  (branch1 branch2 : A)
  : Pif P branch1 branch2 = branch2 := by
  apply choiceInd _ _ (fun x => x = branch2) _ _
  intros a c
  cases c <;> grind

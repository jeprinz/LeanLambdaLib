import Lean.Elab.Tactic

inductive Tree : Type
| Node : Tree → Tree → Tree
| Leaf : Tree
open Tree

theorem rule1 : {a b a' b' : Tree} → Node a b = Node a' b' → a = a' ∧ b = b' := by
  intros _ _ _ _ p
  injection p
  apply And.intro
  assumption
  assumption

theorem asEquation : {a b a' b' : Tree} → (Node a b = Node a' b') = (a = a' ∧ b = b') := by
  intros _ _ _ _
  apply propext
  apply Iff.intro
  intro p
  injection p
  apply And.intro
  assumption
  assumption
  intro x
  rw [And.left x]
  rw [And.right x]

theorem test : {a b : Nat} → (a = b ∧ a = b) → a = b := by
  intro a b ps
  cases ps
  sorry



theorem exampleUseCase : {a b c : Tree} → Node a b = Node c Leaf → (a = c) ∧ (b = Leaf) := by
  intros
  simp [asEquation] at *
  apply And.intro
    sorry
    sorry

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    let mut g ← Lean.Elab.Tactic.getMainGoal
    --
    dbg_trace "blablabla"
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let id := decl.fvarId
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {decl.type}"
    --
    dbg_trace f!"goal type: {goalType}"
    Lean.Elab.admitGoal goal

theorem test_custom_sorry : 1 = 2 := by
  custom_sorry_2

#print test_custom_sorry

theorem sorrytest (cringe : Nat) : 1 = 2 := by
  try rfl
  custom_sorry_2
  try rfl

-- For reference, I looked at mathlib4's tactics at https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Basic.lean
-- In particular, see "clear_aux_decl"

-- The tactic deletes all variables from the context
elab (name := clearAuxDecl) "deletecontext2" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut g ← Lean.Elab.Tactic.getMainGoal
  dbg_trace "delete context 2 running"
  for ldec in ← Lean.MonadLCtx.getLCtx do
    g ← g.tryClear ldec.fvarId
  Lean.Elab.Tactic.replaceMainGoal [g]

theorem test3 (a b c : Nat) (x y z : Bool) : Nat := by
  try rfl
  deletecontext2
  try rfl
  exact 5

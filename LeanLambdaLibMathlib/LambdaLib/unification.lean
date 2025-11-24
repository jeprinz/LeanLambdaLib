import LambdaLib.qterm

open QuotTerm

/-
in this file, i'll define the actual unification tactic
-/

macro "basic_lambda_solve" : tactic => `(tactic|
  repeat ( first
    | simp [lift_app, lift_lam, lift_var, lift_const, subst_app, subst_lam, subst_var,
      liftLiftMulti, substLiftMulti, subst_const, liftMultiZero, beta] at *
    | subst_vars -- TODO: maybe only have this go on equations of type QTerm
  )
)

-- for example, we want this to work:

theorem example1 (t1 t2 : QTerm)
  (H : < (λ x. x) {t1} > = <λ x. x>)
  : <{t1} {t2}> = t2 := by
  --
  basic_lambda_solve
  --

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

inductive NeutralWithArity : Lhs → Nat → QTerm → Prop where
| const : ∀{c}, NeutralWithArity (Lhs.const c) 0 (const c)
| var : ∀{n}, NeutralWithArity (Lhs.var n) 0 (var n)
| app : ∀{lhs t a arg}, NeutralWithArity lhs a t → NeutralWithArity lhs (Nat.succ a) (app t arg)

theorem nwa_inj {t} {lhs1 lhs2} {a1 a2}
  (H1 : NeutralWithArity lhs1 a1 t)
  (H2 : NeutralWithArity lhs2 a2 t)
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
  (H1 : NeutralWithArity lhs1 a1 t1)
  (H2 : NeutralWithArity lhs2 a2 t2)
  (notsame : a1 ≠ a2 ∨ lhs1 ≠ lhs2)
  : t1 ≠ t2 := by
  --
  --
  --
  sorry

import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic

open QuotTerm

-- the idea in this file is to implement programming by typed pattern matching
-- in the rocq version, this ran into transports getting stuck
-- probably lean's proof-irrelevant prop won't help much, but it might help a little.

namespace S
abbrev pair := <λ t1 t2 p. p t1 t2>
abbrev proj1 := <λ p. p (λ x y. x)>
abbrev proj2 := <λ p. p (λ x y. y)>
-- TODO: i can make syntax for pair with a macro, which will run before the elaborator!

-- contexts
abbrev nil := <Nil>
abbrev cons := <Cons> -- takes ctx, lvl, and type

-- variables
abbrev zero := <λ env. {proj2} env>
abbrev succ := <λ x env. x ({proj1} env)>

abbrev pi := <λ x y env. Pi (x env) (λ a. y ({pair} env a))>
abbrev U := <λ env. U>

abbrev lambda := <λ t env a. t ({pair} env a)>
abbrev app := <λ t1 t2 env. (t1 env) (t2 env)>

abbrev weaken := <λ t env. t ({proj1} env)>
abbrev subLast := <λ t toSub env. t ({pair} env (toSub env))>
end S

inductive Var : QTerm → QTerm → QTerm → Prop where
| zero : ∀{ctx T},
  Var <{S.cons} {ctx} {T}> <{S.weaken} {T}> S.zero
| succ : ∀{ctx A T s}, Var ctx A s
  → Var <{S.cons} {ctx} {T}> <{S.weaken} {A}> <{S.succ} {s}>

-- context → level → type → term → prop
inductive Typed : QTerm → QTerm → QTerm → Prop where
| lambda : ∀{ctx A B s},
  Typed <{S.cons} {ctx} {A}> B s
  → Typed ctx <{S.pi} {A} {B}> <{S.lambda} {s}>
| alambda : ∀{ctx A B s},
  Typed ctx S.U A
  → Typed <{S.cons} {ctx} {A}> B s
  → Typed ctx <{S.pi} {A} {B}> <{S.lambda} {s}>
| app : ∀{ctx A B s1 s2}, Typed ctx <{S.pi} {A} {B}> s1 → Typed ctx A s2
  → Typed ctx <{S.subLast} {B} {s2}> <{S.app} {s1} {s2}>
| var : ∀{ctx T t}, Var ctx T t → Typed ctx T t
| U : ∀{ctx}, Typed ctx S.U S.U
| Pi : ∀{ctx A B}, Typed ctx S.U A
  → Typed <{S.cons} {ctx} {A}> S.U B
  → Typed ctx S.U <{S.pi} {A} {B}>

macro "λcast" t:term:10 : term => `(cast (by lambda_solve) $t)

def castVar {ctx1 ctx2 ty1 ty2 tm1 tm2}
  (prog : Var ctx1 ty1 tm1)
  (h1 : ctx1 = ctx2)
  (h3 : ty1 = ty2)
  (h4 : tm1 = tm2)
  : Var ctx2 ty2 tm2 := by
  subst_vars
  exact prog

def castTyped {ctx1 ctx2 ty1 ty2 tm1 tm2}
  (prog : Typed ctx1 ty1 tm1)
  (h1 : ctx1 = ctx2)
  (h3 : ty1 = ty2)
  (h4 : tm1 = tm2)
  : Typed ctx2 ty2 tm2 := by
  subst_vars
  exact prog

macro "castVarM" t:term:10 : term => `(by eapply (castVar $t) <;> (lambda_solve <;> rfl))
macro "castTypedM" t:term:10 : term => `(by eapply (castTyped $t) <;> (lambda_solve <;> rfl))

-- seems like the pair case messes up old things that used to work...
example : Typed S.nil S.U S.U :=
  castTypedM (Typed.app (Typed.lambda (Typed.var Var.zero)) Typed.U)

-- (λ (T : U) (t : T). t) U U
-- example : Typed S.nil S.U S.U :=
--   castTypedM (Typed.app (castTypedM (Typed.app
--     (Typed.alambda Typed.U (Typed.alambda (Typed.var (castVarM Var.zero)) (Typed.var Var.zero)))
--     Typed.U)) Typed.U)

-- uh oh, may need SP. lets see:

-- set_option trace.Meta.Tactic.simp.discharge true

-- inductive Test : Nat → Prop where
-- theorem rewrite_test_2 (n : Nat) (H : Test n) : (n + 1 = n) = True := by sorry
-- example : exists n : Nat, n + 1 = n := by
--   eapply Exists.intro
--   simp (disch := sorry) only [rewrite_test_2]
--   sorry

macro "lambda_solve2" : tactic => `(tactic|
  repeat ( first
    -- | simp at * -- TODO: figure out which lemmas this is using (relating to ∧) and write explicitly
    | fail_if_no_progress subst_vars -- TODO: maybe only have this go on equations of type QTerm
    | casesm* _ ∧ _
    | casesm* QTerm × QTerm
    | simp [*] -- TODO: maybe i can use the `contextual' flag instead
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
    --
    | do_pair_case
    -- NOTE: this next line should be redundant to the call with simp above IF LEAN
    -- WASN'T STUPID. however, disch doesn't work when the goal being dispatched to
    -- has metavariables in it.
    -- | rw [special_case_rw] <;> try (repeat' constructor <;> grind only)
    -- | try (rw [special_case_rw]; pick_goal 2; ((repeat' constructor) <;> grind only))
    -- this one seems like it works, but there is still an infinite loop for some reason
    -- | rw [special_case_rw] at * ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)
    -- the <;> [skip] is necessary to make sure that it ended up with only 1 goal at the end,
    -- to stop the case where it rewrites a metavar and creates more goals.
    | (rw [special_case_rw] at * ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)) <;> [skip]
    | (apply Eq.symm; rw [special_case_rw] at * ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail)) <;> [skip]
  )
)

theorem make_another_goal {T : Prop}  (t : T) (x : False) : T := t

example (t : QTerm) (H : <{liftMulti 2 t} {var 0} {var 0}> = (var 0)) : t = <λ x. x> := by
  lambda_solve2
  --
  -- try (rw [special_case_rw] at * ; pick_goal 2; ((repeat' constructor) <;> grind only))
  -- this seems plausable:
  -- try (rw [special_case_rw] at * ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail))
  -- apply make_another_goal <;>
--     try (rw [special_case_rw] at * ; on_goal 2 => ((repeat' constructor) <;> grind only <;> fail))
--   --

example : Typed S.nil S.U S.U := by
  eapply
    (castTyped (Typed.app (castTyped (Typed.app
    (Typed.alambda Typed.U (Typed.alambda (Typed.var (castVar Var.zero ?a ?b ?c)) (Typed.var Var.zero)))
    Typed.U) ?d ?e ?f) Typed.U) ?g ?h ?i)
  --
  -- superrepeat
  repeat (any_goals (first | fail_if_no_progress lambda_solve2 | rfl))
  --

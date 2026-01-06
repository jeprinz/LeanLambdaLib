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
abbrev Empty := <λ env. Empty>
abbrev Lift := <λ t env. Lift (t env)>

abbrev lambda := <λ t env a. t ({pair} env a)>
abbrev app := <λ t1 t2 env. (t1 env) (t2 env)>

abbrev weaken := <λ t env. t ({proj1} env)>
abbrev subLast := <λ t toSub env. t ({pair} env (toSub env))>

abbrev idSub := <λ env. env>
abbrev weaken1Ren := <λ env. {proj1} env>
abbrev liftSub := <λ sub env. {pair} (sub ({proj1} env)) ({proj2} env)>
abbrev extendSub := <λ sub t env. {pair} (sub env) (t (sub env))>
abbrev subTerm := <λ sub t env. t (sub env)>
end S

inductive Var : QTerm → Nat → QTerm → QTerm → Type where
| zero : ∀{ctx T lvl},
  Var <{S.cons} {ctx} {const (.natConst lvl)} {T}> lvl <{S.weaken} {T}> S.zero
| succ : ∀{ctx A T s lvl1 lvl2}, Var ctx lvl1 A s
  → Var <{S.cons} {ctx} {lvl2} {T}> lvl1 <{S.weaken} {A}> <{S.succ} {s}>

-- context → level → type → term → prop
inductive Typed : QTerm → Nat → QTerm → QTerm → Type where
| lambda : ∀{ctx A B s lvl},
  Typed ctx (Nat.succ lvl) S.U <{S.pi} {A} {B}>
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl B s
  → Typed ctx lvl <{S.pi} {A} {B}> <{S.lambda} {s}>
| app : ∀{ctx A B s1 s2 lvl}, Typed ctx lvl <{S.pi} {A} {B}> s1 → Typed ctx lvl A s2
  → Typed ctx lvl <{S.subLast} {B} {s2}> <{S.app} {s1} {s2}>
| var : ∀{ctx T t lvl}, Var ctx lvl T t → Typed ctx lvl T t
| Empty : ∀{ctx}, Typed ctx 1 S.U S.Empty
| U : ∀{ctx} {lvl : Nat}, Typed ctx lvl.succ.succ S.U S.U
| Pi : ∀{ctx lvl A B}, Typed ctx lvl.succ S.U A
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl.succ S.U B
  → Typed ctx lvl.succ S.U <{S.pi} {A} {B}>
| Lift : ∀{ctx T} {lvl : Nat}, Typed ctx lvl.succ S.U T → Typed ctx lvl.succ.succ S.U <{S.Lift} {T}>
| lift : ∀{ctx lvl T t}, Typed ctx lvl T t → Typed ctx lvl.succ <{S.Lift} {T}> t
| lower : ∀{ctx lvl T t}, Typed ctx lvl.succ <{S.Lift} {T}> t → Typed ctx lvl T t

def Ren (sub ctx1 ctx2 : QTerm) : Type :=
    ∀{lvl T t}, Var ctx1 lvl T t → Var ctx2 lvl <{S.subTerm} {sub} {T}> <{S.subTerm} {sub} {t}>

macro "λcast" t:term:10 : term => `(cast (by lambda_solve) $t)

def idRen {ctx : QTerm} : Ren S.idSub ctx ctx :=
    -- fun x ↦ by lambda_solve; exact x
    fun x ↦ λcast x

/-
i'm going to need a macro/elaborator which:
given x of some inductive type, automatically generalizes all of the indices
then, you can do a match with match cases.
some thing like
gmatch x with
|... the cases

can i somehow get it to then turn into a normal match?


one stupid way to solve this problem is to rewrite Var and Typed so that
the output just has variables, and there are extra preises with equalities
-/

-- syntax:1500 (name := caster) "<" lambda_scope:10 ">" : term

def cast2.{u} {α β : Sort u} (a : α) (h : α = β) : β := cast h a

def castVar {ctx1 ctx2 lvl1 lvl2 ty1 ty2 tm1 tm2}
  (prog : Var ctx1 lvl1 ty1 tm1)
  (h1 : ctx1 = ctx2)
  (h2 : lvl1 = lvl2)
  (h3 : ty1 = ty2)
  (h4 : tm1 = tm2)
  : Var ctx2 lvl2 ty2 tm2 := by
  subst_vars
  exact prog

/-
the issue is that in the rocq version in metaprogramming/substitution.v,
after refining with castVar, the three arguments to Var.zero are left as evars.
in rocq, evars can exist across goals, and solving for them in one goal will
solve for them in other goals.

in lean, i'm not sure if evars like this exist.
if they don't, then i don't really see how this sort of pattern matching could be
possible at all.

see https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md
the matchlib tactic eapply.
so something must be possible here.
-/

def liftRen {ctx1 ctx2 lvl T sub} (ren : Ren sub ctx1 ctx2)
    : Ren <{S.liftSub} {sub}> <{S.cons} {ctx1} {lvl} {T}> <{S.cons} {ctx2} {lvl} ({S.subTerm} {sub} {T})>
    := fun x ↦ by
    generalize h : <{S.cons} {ctx1} {lvl} {T}> = ctx at x
    -- exact match bla : x with
    exact match x with
    -- match (generalizing := false) bla : x with
    | Var.zero => by
        -- the question is, how can i leave the inputs of Var.zero to be metavariables that
        -- can be solved in later goals?
        -- refine (castVar (@Var.zero ?a ?b ?c) ?d ?e ?f ?g)
        eapply (castVar Var.zero)
        · --
          --
          sorry
        · --
          -- lambda_solve
          simp (disch := repeat constructor) only [ app_fact_rw, ] at *
          repeat ( first
            -- | simp at * -- TODO: figure out which lemmas this is using (relating to ∧) and write explicitly
            | fail_if_no_progress subst_vars -- TODO: maybe only have this go on equations of type QTerm
            | casesm* _ ∧ _
            | casesm* QTerm × QTerm
            | normalize
            | simp only [lam_body_rw, const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2,
              SynTerm.Constant.strConst.injEq, String.reduceEq] at *
            | simp [*] -- TODO: maybe i can use the `contextual' flag instead
            | simp (disch := (repeat' constructor) <;> grind only) only [eta_contract]
            | simp (disch := repeat constructor) only [app_fact_rw, app_ne_const_rw, app_ne_var_rw,
              app_ne_const_rw2, app_ne_var_rw2] at *
          )
          --
          simp (disch := repeat constructor) only [ app_fact_rw, ] at *
          simp (disch := repeat constructor) only [ app_fact_rw, ] at *
          simp (disch := repeat constructor) only [ app_fact_rw, ] at *
          simp (disch := repeat constructor) only [ app_fact_rw, ] at *
          simp (disch := repeat constructor) only [ app_fact_rw, ] at *
          --
          sorry
        · --
          --
          sorry
        · --
          --
          sorry
        · --
          --
          sorry
        · --
          --
          sorry
        · --
          --
          sorry
        --
        -- convert Var.zero <;> lambda_solve
        -- refine (cast ?_ Var.zero)
        -- exact (cast2 (by lambda_solve) Var.zero)
        --
        -- sorry
    | Var.succ x' => _

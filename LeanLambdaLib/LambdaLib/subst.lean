import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic

open QuotTerm

-- the idea in this file is to implement programming by typed pattern matching
-- in the rocq version, this ran into transports getting stuck
-- probably lean's proof-irrelevant prop won't help much, but it might help a little.
-- NOTE: see https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
-- specifically, 13.5.9. Cast Management
-- and https://arxiv.org/pdf/2001.10594

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
| app : ∀{ctx A B s1 s2}, Typed ctx <{S.pi} {A} {B}> s1 → Typed ctx A s2
  → Typed ctx <{S.subLast} {B} {s2}> <{S.app} {s1} {s2}>
| var : ∀{ctx T t}, Var ctx T t → Typed ctx T t
| Empty : ∀{ctx}, Typed ctx S.U S.Empty
| U : ∀{ctx}, Typed ctx S.U S.U
| Pi : ∀{ctx A B}, Typed ctx S.U A
  → Typed <{S.cons} {ctx} {A}> S.U B
  → Typed ctx S.U <{S.pi} {A} {B}>

def Ren (sub ctx1 ctx2 : QTerm) : Prop :=
    ∀{T t}, Var ctx1 T t → Var ctx2 <{S.subTerm} {sub} {T}> <{S.subTerm} {sub} {t}>

macro "λcast" t:term:10 : term => `(cast (by lambda_solve) $t)

def idRen {ctx : QTerm} : Ren S.idSub ctx ctx :=
    -- fun x ↦ by lambda_solve; exact x
    fun x ↦ λcast x


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

def liftRen {ctx1 ctx2 T sub} (ren : Ren sub ctx1 ctx2)
    : Ren <{S.liftSub} {sub}> <{S.cons} {ctx1} {T}> <{S.cons} {ctx2} ({S.subTerm} {sub} {T})>
    := fun x ↦ by
    generalize h : <{S.cons} {ctx1} {T}> = ctx at x
    exact match x with
    | Var.zero => by
        eapply (castVar Var.zero) <;> (lambda_solve <;> rfl)
    | Var.succ x' => by
      eapply (castVar (Var.succ (ren (castVar x' ?_ ?_ ?_))))
        <;> (lambda_solve <;> rfl)

def weaken1Ren {ctx T} : Ren S.weaken1Ren ctx <{S.cons} {ctx} {T}> :=
  fun x ↦ by
  eapply (castVar (Var.succ x)) <;> (lambda_solve <;> rfl)

axiom hole.{u} {T : Sort u} : T

macro "castVarM" t:term:10 : term => `(by eapply (castVar $t) <;> (lambda_solve <;> rfl))
macro "castTypedM" t:term:10 : term => `(by eapply (castTyped $t) <;> (lambda_solve <;> rfl))

def renTerm {ctx1 ctx2 sub T t} (ren : Ren sub ctx1 ctx2)
  (prog : Typed ctx1 T t) : Typed ctx2 <{S.subTerm} {sub} {T}> <{S.subTerm} {sub} {t}> :=
  match prog with
  | .lambda t => castTypedM (Typed.lambda (renTerm (liftRen ren) t))
  | @Typed.app ctx A B s1 s2 t1 t2 => by
      apply (castTyped (@Typed.app ctx2
        <{S.subTerm} {sub} {A}>
        <{S.subTerm} ({S.liftSub} {sub}) {B}>
        <{S.subTerm} {sub} {s1}>
        <{S.subTerm} {sub} {s2}>
        (castTyped (renTerm ren t1) _ _ _)
        (castTyped (renTerm ren t2) _ _ _)) _ _ _) <;> (try (lambda_solve <;> rfl))
  | .var x => castTypedM (Typed.var (ren (castVarM x)))
  | .Empty => castTypedM .Empty
  | .U => castTypedM .U
  | .Pi a b => castTypedM (Typed.Pi (castTypedM (renTerm ren a))
    (castTypedM (renTerm (liftRen ren) b)))

example : True := by simp

-- text an example of running it
def term1 : Typed S.nil <{S.pi} {S.U} ({S.weaken} {S.U})> <{S.lambda} {S.zero}> :=
  Typed.lambda (Typed.var Var.zero)

#check HEq
set_option pp.proofs true
example : renTerm idRen term1 ≍ term1 := by
  unfold term1
  --
  simp [renTerm]
  --
  sorry

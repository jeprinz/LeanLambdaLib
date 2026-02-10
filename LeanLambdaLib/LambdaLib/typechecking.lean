import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic



open QuotTerm

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

def mycast {A B} (a : A) (h : A = B) : B := cast h a
macro "mega_lambda_solve" : tactic => `(tactic|
  repeat (any_goals (first | fail_if_no_progress lambda_solve | rfl | congr 1)))

-- macro "{" t:term:10 "}" : term => `(mycast $t ?_)
macro "{" t:term:10 "}" : term => `(mycast $t ?_)

-- (λ (T : Type). λ (t : T). t) Type Type
example : Typed S.nil S.U S.U := by
  eapply {Typed.app {Typed.app (.alambda .U (.alambda (.var {Var.zero}) (.var .zero))) .U} .U}
  --
  mega_lambda_solve
  --
  -- iterate 7 rotate_left
  -- congr 1
  -- lambda_solve
  -- rotate_left
  -- --
  -- -- congr 1 <;> normalize
  -- -- -- TODO: i need to fix lambda_solve pair case so that this next line WOULDN'T simplify this!!!
  -- -- lambda_solve -- this shouldn't do the pair case, since its not vars!
  -- --
  -- rotate_right
  -- -- OK, here we are
  -- congr 1
  -- --
  -- --
  -- lambda_solve <;> rfl
  -- --
  -- normalize
  -- --
  -- lambda_solve
  -- -- mega_lambda_solve
  -- --

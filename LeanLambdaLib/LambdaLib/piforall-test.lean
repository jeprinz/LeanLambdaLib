import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic

-- this is testing that i can typecheck the church definitions from
-- https://github.com/sweirich/pi-forall/blob/2023/version3/test/NatChurch.pi
-- i can't typecheck the scott definitions without adding general recursion
-- to the embedding


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

-- for more convenient function types
abbrev arrow := <λ a b. {pi} a ({weaken} b)>
end S

inductive Var : QTerm → QTerm → QTerm → Type where
| zero : ∀{ctx T},
  Var <{S.cons} {ctx} {T}> <{S.weaken} {T}> S.zero
| succ : ∀{ctx A T s}, Var ctx A s
  → Var <{S.cons} {ctx} {T}> <{S.weaken} {A}> <{S.succ} {s}>

-- context → level → type → term → Type
inductive Typed : QTerm → QTerm → QTerm → Type where
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

open Typed
open Var

theorem congrTyped {ctx1 ctx2 T1 T2 t1 t2}
  : ctx1 = ctx2 → T1 = T2 → t1 = t2 → Typed ctx1 T1 t1 = Typed ctx2 T2 t1 := by
  intros
  subst_vars
  rfl

theorem congrVar {ctx1 ctx2 T1 T2 t1 t2}
  : ctx1 = ctx2 → T1 = T2 → t1 = t2 → Var ctx1 T1 t1 = Var ctx2 T2 t1 := by
  intros
  subst_vars
  rfl

def mycast {A B} (a : A) (h : A = B) : B := cast h a

-- macro "{" t:term:10 "}" : term => `(mycast $t ?_)
macro "{{" t:term:10 "}}" : term => `(mycast $t ?_)

def ann.{u} (T : Type u) (t : T) := t
def of {ctx T t} (_ : Typed ctx T t) : QTerm := t

-- there were problems with (congr 1) doing stuff to equations
-- on lambda terms where it assumes nonsense. we want to only do congruence when
-- Typed or Var are equal.
-- macro "mega_lambda_solve" : tactic => `(tactic|
--   repeat (any_goals (first | apply And.intro |
--             fail_if_no_progress lambda_solve | rfl | congr 1)))
macro "mega_lambda_solve" : tactic => `(tactic|
  repeat (any_goals (first | apply And.intro | apply congrTyped | apply congrVar |
            fail_if_no_progress lambda_solve | rfl)))

-- def nat := ((by eapply U) : Typed S.nil S.U _)
def nat := ann (Typed S.nil S.U _) (by
  eapply (Pi U (Pi (.var {{Var.zero}})
    (Pi (Pi (.var {{Var.succ .zero}}) (.var {{Var.succ (.succ .zero)}}))
      (.var {{Var.succ (.succ .zero)}}))))
  mega_lambda_solve
  --
)

def z := ann (Typed S.nil (of nat) _) (by
  simp [of]
  eapply {{lambda (lambda (lambda (.var (.succ .zero))))}}
  mega_lambda_solve
  --
)


example : True := by grind

def s := ann (Typed S.nil <{S.arrow} {of nat} {of nat}> _) (by
  simp [of]
  normalize
  eapply {{Typed.lambda (lambda (lambda (lambda
    (Typed.app (.var {{Var.zero}})
      (Typed.app {{Typed.app {{Typed.app {{Typed.var zero.succ.succ.succ}}
        {{Typed.var zero.succ.succ}}}}
        {{Typed.var zero.succ}}}}
        {{Typed.var zero}})))))}}
  mega_lambda_solve
  --
)

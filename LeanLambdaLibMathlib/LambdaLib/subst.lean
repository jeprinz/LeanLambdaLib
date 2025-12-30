import LambdaLib.qterm
import LambdaLib.unification

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

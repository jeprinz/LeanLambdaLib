import LambdaLib.qterm
import LambdaLib.unification

open QuotTerm

-- in this file, i'll define dependent type theory and prove canonicity

namespace S
abbrev pair := <λ t1 t2 p. p t1 t2>
abbrev proj1 := <λ p. p (λ x y. x)>
abbrev proj2 := <λ p. p (λ x y. y)>
-- TODO: i can make syntax for pair with a macro, which will run before the elaborator!

-- contexts
def nil := <Nil>
def cons := <λ ctx lvl ty. Cons ctx lvl ty>

-- variables
def zero := <λ env. {proj2} env>
def succ := <λ x env. x ({proj1} env)>

def pi := <λ x y env. Pi (x env) (λ x. y ({pair} env a))>
def U := <λ env. U>
def Empty := <λ env. Empty>
def Lift := <λ T env. Lift (T env)>

def lambda := <λ t env a. t ({pair} env a)>
def app := <λ t1 t2 env. (t1 env) (t2 env)>

def weaken := <λ t env. t ({proj1} env)>
def subLast := <λ t toSub env. t ({pair} env (toSub env))>
end S

inductive VarTyped : QTerm → Nat → QTerm → QTerm → Prop where
| zero : ∀{ctx T lvl},
  VarTyped <{S.cons} {ctx} {const (.natConst lvl)} {T}> lvl <{S.weaken} {T}> zero
| succ : ∀{ctx A T s lvl1 lvl2}, VarTyped ctx lvl1 A s
  → VarTyped <{S.cons} {ctx} {lvl2} {T}> lvl1 <{S.weaken} {A}> <{succ} {s}>

-- context → level → type → term → prop
inductive Typed : QTerm → Nat → QTerm → QTerm → Prop where
| lambda : ∀{ctx A B s lvl}, Typed ctx (Nat.succ lvl) S.U <{S.pi} {A} {B}>
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl B s
  → Typed ctx lvl <{S.pi} {A} {B}> <{S.lambda} {s}>
| app : ∀{ctx A B s1 s2 lvl}, Typed ctx lvl <{S.pi} {A} {B}> s1 → Typed ctx lvl A s2
  → Typed ctx lvl <{S.subLast} {B} {s2}> <{S.app} {s1} {s2}>
| var : ∀{ctx T t lvl}, VarTyped ctx lvl T t → Typed ctx lvl T t
| Empty : ∀{ctx}, Typed ctx 1 S.U S.Empty
| U : ∀{ctx lvl}, Typed ctx (2 + lvl) S.U S.U
| Lift : ∀{ctx lvl T}, Typed ctx (1 + lvl) S.U T → Typed ctx (2 + lvl) S.U <{S.Lift} {T}>
| lift : ∀{ctx lvl T t}, Typed ctx lvl T t → Typed ctx (1 + lvl) <{S.Lift} {T}> t
| lower : ∀{ctx lvl T t}, Typed ctx (1 + lvl) <{S.Lift} {T}> t → Typed ctx lvl T t

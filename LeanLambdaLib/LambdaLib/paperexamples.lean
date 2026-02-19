import LambdaLib.qterm
import LambdaLib.unification

inductive ty : Type where
| arrow : ty → ty → ty
| base : ty

def Γ := List ty

inductive Var : Γ → ty → Type where
| zero : ∀ {Γ ty}, Var (ty :: Γ) ty
| succ : ∀ {Γ A B}, Var Γ A → Var (B :: Γ) A

inductive Deriv : Γ → ty → Type where
| var : ∀ {Γ ty}, Var Γ ty → Deriv Γ ty
| lambda : ∀ {Γ A B}, Deriv (A :: Γ) B → Deriv Γ (.arrow A B)
| app : ∀ {Γ A B}, Deriv Γ (.arrow A B) → Deriv Γ A → Deriv Γ B
| tt : ∀ {Γ}, Deriv Γ .base

def prog : Deriv [] .base :=
  .app (.lambda (.var .zero)) .tt

def prog2 : Deriv [] (.arrow (.arrow .base .base) (.arrow .base .base)) :=
  .lambda (.lambda (.app (.var (.succ .zero)) (.var .zero)))

open QuotTerm

abbrev two' : QTerm := <λ s z. s (s z)>

example
(t : QTerm)
(H : <{two'} S Z> = <S {t}>)
: t = <S Z>
:= by
  lambda_solve
  --

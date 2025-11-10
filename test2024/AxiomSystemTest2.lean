
/--
Clearly there are some annoying redundancies in this axiomatic system -
like why are there two things, data and props?
Arrows at two different levels.
But I still think that this one is interesting to think about,
because it doesn't need type levels and can recover a lot very simply.
-/

inductive Ty : Type where
| Proposition : Ty
| Data : Ty
| Arrow : Ty -> Ty -> Ty
open Ty

inductive PContext : Type where
| Nil : PContext
| cons : PContext -> Ty -> PContext
open PContext

inductive TVar : PContext -> Ty -> Type where
| zero : ∀{Γ T}, TVar (cons Γ T) T
| suc : ∀{Γ A B}, TVar Γ A → TVar (cons Γ B) A

inductive Propo : PContext -> Ty -> Type where
-- Propositions
| forall: ∀ {n} , (T : Ty) -> Propo (cons n T) Proposition → Propo n Proposition
| arrow : ∀ {Γ}, Propo Γ Proposition → Propo Γ Proposition → Propo Γ Proposition
-- Definitions
| apply : ∀ {Γ A B}, Propo Γ (Arrow A B) → Propo Γ A → Propo Γ B
| TVar : ∀ {Γ T}, TVar Γ T → Propo Γ T
| lambda : ∀{Γ A B}, Propo (cons Γ A) B → Propo Γ (Arrow A B)
| lett : ∀{Γ A B}, Propo Γ A → Propo (cons Γ A) B → Propo Γ B

def Ren : PContext → PContext → Type :=
  fun Γ₁ Γ₂ => ∀{T}, TVar Γ₁ T → TVar Γ₂ T

def liftRen {Γ₁ Γ₂ T} (ren : Ren Γ₁ Γ₂) : Ren (cons Γ₁ T) (cons Γ₂ T) :=
  fun x =>
    match x with
    | TVar.zero => TVar.zero
    | TVar.suc x => TVar.suc (ren x)

def rename {Γ₁ Γ₂ T} (ren : Ren Γ₁ Γ₂) (p : Propo Γ₁ T) : Propo Γ₂ T :=
  match p with
  | Propo.forall t p => Propo.forall t (rename (liftRen ren) p)
  | Propo.TVar pv => Propo.TVar (ren pv)
  | Propo.arrow p1 p2 => Propo.arrow (rename ren p1) (rename ren p2)
  | Propo.lambda t => Propo.lambda (rename (liftRen ren) t)
  | Propo.apply t1 t2 => Propo.apply (rename ren t1) (rename ren t2)
  | Propo.lett deff body => Propo.lett (rename ren deff) (rename (liftRen ren) body)

def Subst : PContext → PContext → Type :=
  fun Γ₁ Γ₂ => ∀{T}, TVar Γ₁ T → Propo Γ₂ T

def liftSub {Γ₁ Γ₂ T} (sub : Subst Γ₁ Γ₂) : Subst (cons Γ₁ T) (cons Γ₂ T) :=
  fun x =>
    match x with
    | TVar.zero => Propo.TVar TVar.zero
    | TVar.suc x => rename TVar.suc (sub x)

def subLast {Δ T} (p : Propo Δ T) : Subst (cons Δ T) Δ :=
  fun i => match i with
    | TVar.zero => p
    | TVar.suc x => Propo.TVar x

def sub {Γ₁ Γ₂ T} (subst : Subst Γ₁ Γ₂) (p : Propo Γ₁ T) : Propo Γ₂ T :=
  match p with
  | Propo.forall t p => Propo.forall t (sub (liftSub subst) p)
  | Propo.TVar pv => subst pv
  | Propo.arrow p1 p2 => Propo.arrow (sub subst p1) (sub subst p2)
  | Propo.lambda t => Propo.lambda (sub (liftSub subst) t)
  | Propo.apply t1 t2 => Propo.apply (sub subst t1) (sub subst t2)
  | Propo.lett deff body => Propo.lett (sub subst deff) (sub (liftSub subst) body)

inductive Context : PContext → Type where
| Nil : Context Nil
| cons : ∀{Γ}, Context Γ -> (T : Ty) -> Context (cons Γ T)
| propCons : ∀{Γ}, Context Γ → Propo Γ Proposition → Context Γ
-- Did I just find a trick that makes it easy to define system F? The way that this is parametrized?

inductive Var : {Γ : PContext} → Context Γ → Propo Γ Proposition → Type where
| zero : ∀{Γ T} {Δ : Context Γ}, Var (Context.propCons Δ T) T
| suc : ∀{Γ A B} {Δ : Context Γ}, Var Δ A → Var (Context.propCons Δ B) A

inductive Proof : {Γ : PContext} → (Context Γ) → Propo Γ Proposition -> Type where
| Tlambda : ∀{Γ P} {Δ : Context Γ}, Proof (Context.cons Δ T) P → Proof Δ (Propo.forall T P)
| lambda : ∀{Γ A B} {Δ : Context Γ}, Proof (Context.propCons Δ A) B → Proof Δ (Propo.arrow A B)
| apply : ∀{Γ A B} {Δ : Context Γ}, Proof Δ (Propo.arrow A B) → Proof Δ A → Proof Δ B
| Tapply : ∀{Γ T} {P : Propo (cons Γ T) Proposition} {Δ : Context Γ},
    Proof Δ (Propo.forall T P)
    → (arg : Propo Γ T)
    → Proof Δ (sub (subLast arg) P)
| var : ∀{Γ T} {Δ : Context Γ}, Var Δ T → Proof Δ T

---------------------------------------------------------------------------
----------------------Shallow Embedding into Lean -------------------------
---------------------------------------------------------------------------

inductive Data : Type :=
| ctr : string -> List Data -> Data

-- What would go wrong in Agda, without impredicativity? Or would this work? That can't be right.
def decodeTy (ty : Ty) : Type :=
  match ty with
  | Ty.Proposition => Prop
  | Ty.Arrow A B => decodeTy A -> decodeTy B
  | Ty.Data => Data

def decodePContext (Γ : PContext) : Type :=
  match Γ with
  | Nil => Unit
  | cons Γ t => decodePContext Γ × decodeTy t

def decodeTVar {Γ : PContext} {T : Ty} (γ : decodePContext Γ) (x : TVar Γ T) : decodeTy T :=
  match x, γ with
  | TVar.zero, (_γ, t) => t
  | TVar.suc x, (γ, _t) => decodeTVar γ x

def decodePropo {Γ T} (γ : decodePContext Γ) (prop : Propo Γ T) : decodeTy T :=
  match prop with
  | Propo.forall t p => (x : decodeTy t) -> decodePropo (γ, x) p
  | Propo.TVar pv => decodeTVar γ pv
  | Propo.arrow p1 p2 => decodePropo γ p1 → decodePropo γ p2
  | Propo.lambda t => fun x => decodePropo (γ, x) t
  | Propo.apply t1 t2 => (decodePropo γ t1) (decodePropo γ t2)
  | Propo.lett deff body => let x := decodePropo γ deff ; decodePropo (γ, x) body


def decodeContext {Γ : PContext} (Δ : Context Γ) (γ : decodePContext Γ) : Type :=
  match Δ, γ with
  | Context.Nil, () => Unit
  | Context.cons Δ t, (γ, _) => decodeContext Δ γ × decodeTy t
  | Context.propCons Δ P, γ => Σ' _δ : decodeContext Δ γ, decodePropo γ P

def decodeProof {Γ P} {Δ : Context Γ} (γ : decodePContext Γ) (δ : decodeContext Δ γ) (proof : Proof Δ P) : decodePropo γ P :=
  match proof with
  | Proof.Tlambda t => fun x => decodeProof (γ, x) (δ, x) t
  -- Why does it work by entering and existing tactic mode but not otherwise...
  -- | Proof.lambda t => fun x => decodeProof γ ⟨δ, x⟩ t
  | Proof.lambda t => fun x => decodeProof γ (by exact ⟨δ, x⟩) t
  | Proof.apply t1 t2 => (decodeProof γ δ t1) (decodeProof γ δ t2)
  | Proof.Tapply t arg => let thing := (decodeProof γ δ t) (decodePropo γ arg); _
  | Proof.var x => _


/-
TODO: Put this in notes file somewhere.

Thought (In dependent type theory):
You could do (v : Vector T n),
or (l : List T), (p : length l n)
. But the latter annoyingly splits it into two pieces.

In this kind of system from this file though, the former would be:
v : Data, and a proposition "v is Vector T n"
the second would be:
v : Data, and a proposition "v is list T, and length n".

So basically, by making them both shitty, the second is no less shitty than the former.
And in fact, these two distinct ideas become one idea.

Is this good, because I need not distinguish between Vector and List + Prop?
Or bad, because I can't get it into one premise of one type?
-/

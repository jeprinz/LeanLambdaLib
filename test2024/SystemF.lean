def TContext := Nat

inductive TVar : TContext → Type where
  | zero : ∀{n}, TVar (Nat.succ n)
  | succ : ∀{n}, TVar n → TVar (Nat.succ n)

inductive Ty : TContext -> Type where
-- Propositions
| forall: ∀ {n}, Ty (Nat.succ n) → Ty n
| arrow : ∀ {Γ}, Ty Γ → Ty Γ → Ty Γ
| TVar : ∀ {Γ}, TVar Γ → Ty Γ

def Ren : TContext → TContext → Type :=
  fun Γ₁ Γ₂ => TVar Γ₁ → TVar Γ₂

def liftRen {Γ₁ Γ₂} (ren : Ren Γ₁ Γ₂) : Ren (Nat.succ Γ₁) (Nat.succ Γ₂) :=
  fun x =>
    match x with
    | TVar.zero => TVar.zero
    | TVar.succ x => TVar.succ (ren x)

def rename {Γ₁ Γ₂} (ren : Ren Γ₁ Γ₂) (p : Ty Γ₁) : Ty Γ₂ :=
  match p with
  | Ty.forall p => Ty.forall (rename (liftRen ren) p)
  | Ty.TVar pv => Ty.TVar (ren pv)
  | Ty.arrow p1 p2 => Ty.arrow (rename ren p1) (rename ren p2)

def Subst : TContext → TContext → Type :=
  fun Γ₁ Γ₂ => TVar Γ₁ → Ty Γ₂

def liftSub {Γ₁ Γ₂} (sub : Subst Γ₁ Γ₂) : Subst (Nat.succ Γ₁) (Nat.succ Γ₂):=
  fun x =>
    match x with
    | TVar.zero => Ty.TVar TVar.zero
    | TVar.succ x => rename TVar.succ (sub x)

def subLast {Δ} (p : Ty Δ) : Subst (Nat.succ Δ) Δ :=
  fun i => match i with
    | TVar.zero => p
    | TVar.succ x => Ty.TVar x

def sub {Γ₁ Γ₂} (subst : Subst Γ₁ Γ₂) (p : Ty Γ₁) : Ty Γ₂ :=
  match p with
  | Ty.forall p => Ty.forall (sub (liftSub subst) p)
  | Ty.TVar pv => subst pv
  | Ty.arrow p1 p2 => Ty.arrow (sub subst p1) (sub subst p2)

inductive Context : TContext → Type where
| Nil : Context Nil
| cons : ∀{Γ}, Context Γ -> Context (Nat.succ Γ)
| propCons : ∀{Γ}, Context Γ → Ty Γ → Context Γ
-- Did I just find a trick that makes it easy to define system F? The way that this is parametrized?

inductive Var : {Γ : TContext} → Context Γ → Ty Γ → Type where
| zero : ∀{Γ T} {Δ : Context Γ}, Var (Context.propCons Δ T) T
| suc : ∀{Γ A B} {Δ : Context Γ}, Var Δ A → Var (Context.propCons Δ B) A
| suc' : ∀{Γ A} {Δ : Context Γ}, Var Δ A → Var (Context.cons Δ) (rename TVar.succ A)

inductive Term : {Γ : TContext} → (Context Γ) → Ty Γ -> Type where
| Tlambda : ∀{Γ P} {Δ : Context Γ}, Term (Context.cons Δ) P → Term Δ (Ty.forall P)
| lambda : ∀{Γ A B} {Δ : Context Γ}, Term (Context.propCons Δ A) B → Term Δ (Ty.arrow A B)
| apply : ∀{Γ A B} {Δ : Context Γ}, Term Δ (Ty.arrow A B) → Term Δ A → Term Δ B
| Tapply : ∀{Γ} {P : Ty (Nat.succ Γ)} {Δ : Context Γ},
    Term Δ (Ty.forall P)
    → (arg : Ty Γ)
    → Term Δ (sub (subLast arg) P)
| var : ∀{Γ T} {Δ : Context Γ}, Var Δ T → Term Δ T

---------------------------------------------------------------------------
----------------------Shallow Embedding into Lean -------------------------
---------------------------------------------------------------------------

def decodeTContext (Γ : TContext) : Type :=
  match Γ with
  | Nat.zero => Unit
  | Nat.succ Γ => decodeTContext Γ × Prop

def decodeTVar {Γ : TContext} (γ : decodeTContext Γ) (x : TVar Γ) : Prop :=
  match x, γ with
  | TVar.zero, (_γ, t) => t
  | TVar.succ x, (γ, _t) => decodeTVar γ x

def decodeTy {Γ} (γ : decodeTContext Γ) (ty : Ty Γ) : Prop :=
  match ty with
  | Ty.forall p => (x : Prop) -> decodeTy (γ, x) p
  | Ty.TVar pv => decodeTVar γ pv
  | Ty.arrow p1 p2 => decodeTy γ p1 → decodeTy γ p2


def decodeContext {Γ : TContext} (Δ : Context Γ) (γ : decodeTContext Γ) : Type :=
  match Δ, γ with
  -- | Context.Nil, () => Unit
  -- | Context.cons Δ t, (γ, _) => decodeContext Δ γ × decodeTy t
  -- | Context.propCons Δ P, γ => Σ' _δ : decodeContext Δ γ, decodeTy γ P
  | Context.Nil, _x => Unit
  | Context.cons Δ, (γ, _) => decodeContext Δ γ × Prop
  | Context.propCons Δ P, γ => Σ' _δ : decodeContext Δ γ, decodeTy γ P

def decodeVar {Γ P} {Δ : Context Γ} (γ : decodeTContext Γ) (δ : decodeContext Δ γ)
  (i : Var Δ P) : decodeTy γ P :=
  match P, Γ, Δ, i, γ, δ with
  | _, _, (Context.propCons Γ' _), Var.zero, _, ⟨_δ, t⟩ => t
  | _, _, _, Var.suc i, _, _ => _
  | _, _, _, Var.suc' i, _, _ => _

def decodeTerm {Γ P} {Δ : Context Γ} (γ : decodeTContext Γ) (δ : decodeContext Δ γ)
  (t : Term Δ P) : decodeTy γ P :=
  match t with
  | Term.Tlambda t => fun x => decodeTerm (γ, x) (δ, x) t
  -- Why does it work by entering and existing tactic mode but not otherwise...
  -- | Term.lambda t => fun x => decodeTerm γ ⟨δ, x⟩ t
  | Term.lambda t => fun x => decodeTerm γ (by exact ⟨δ, x⟩) t
  | Term.apply t1 t2 => (decodeTerm γ δ t1) (decodeTerm γ δ t2)
  | Term.Tapply t arg => let thing := (decodeTerm γ δ t) (decodeTy γ arg); _
  | Term.var x => _

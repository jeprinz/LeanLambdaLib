
/--
Clearly there are some annoying redundancies in this axiomatic system -
like why are there two things, data and props?
But I still think that this one is interesting to think about,
because it doesn't need type levels and can recover a lot very simply.
-/

inductive Ty : Type where
| Proposition : List Ty → Ty
| Data : Ty
open Ty

inductive PContext : Type where
| Nil : PContext
| cons : PContext -> Ty -> PContext
-- | cons: (Γ : Context) -> Proposition Γ → Context
open PContext

inductive PVar : PContext -> Type where
| zero : ∀{Γ T}, PVar (cons Γ T)
-- | suc : ∀{Γ A B}, PVar Γ

mutual

  inductive Proposition : PContext -> Type where
  -- Quantification is always over (.... -> Prop)
  | forall: ∀ n , (t : Ty) -> Proposition (cons n t) → Proposition n
  | apply : ∀ n, PVar n → _ → Proposition n
  | arrow : ∀ {Γ}, Proposition Γ → Proposition Γ → Proposition Γ

end

---------------------------------------------------------------------------
----------------------Shallow Embedding into Lean -------------------------
---------------------------------------------------------------------------

inductive Data : Type :=
| ctr : string -> List Data -> Data

mutual
  def decodeTy (ty : Ty) : Type :=
    match ty with
    | Ty.Proposition tys => decodeTys tys → Prop
    | Ty.Data => Data

  def decodeTys (tys : List Ty) : Type :=
    match tys with
    | List.nil => Unit
    | List.cons ty tys => decodeTy ty × decodeTys tys
end

def decodePContext (Γ : PContext) : Type :=
  match Γ with
  | Nil => Unit
  | cons Γ t => decodePContext Γ × decodeTy t

def decodePVar {Γ : PContext} (γ : decodePContext Γ) (x : PVar Γ)  : Prop :=
  match x with
  -- |

def decodeProp {Γ : PContext} (γ : decodePContext Γ) (prop : Proposition Γ)  : Prop :=
  match prop with
  | Proposition.forall n t p => (x : decodeTy t) -> decodeProp (γ, x) p
  | Proposition.var n pv => _
  | Proposition.arrow p1 p2 => decodeProp γ p1 → decodeProp γ p2


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

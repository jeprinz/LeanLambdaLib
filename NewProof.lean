-- This file is a translation of PLFA

-- https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html

--------------------------------------------------------------------------------
---------- This section came from Untyped.agda in plfa -------------------------
--------------------------------------------------------------------------------


open Nat
open Fin
open Option

def Context : Type := Nat
-- def Var : Context → Type := Fin

inductive Var : Context → Type 
| zero : ∀ {Γ}, Var (succ Γ)
| succ : ∀ {Γ}, Var Γ → Var (succ Γ) 

theorem noVarZero : Var zero → False := by
  let gen : (∀{n}, Var n → n = zero → False) := by
    intro n x
    induction x with
    | zero => simp
    | succ _ =>  simp
  intro x
  apply gen
  apply x
  rfl

inductive Term : Context → Type  
| var : ∀ {Γ}, Var Γ → Term Γ 
| lam : ∀ {Γ}, Term (succ Γ) → Term Γ
| app : ∀ {Γ}, Term Γ → Term Γ → Term Γ  

open Term

def Ren (n1 n2 : Context) : Type := Var n1 → Var n2 

def ext {n1 n2} (ren1 : Ren n1 n2) : (Ren (succ n1) (succ n2))
  := fun x => match x with
              | Var.zero => Var.zero
              | Var.succ x' => Var.succ (ren1 x')

def rename {n1 n2} (ren : Ren n1 n2) (t : Term n1) : Term n2 :=
  match t with
  | var i => var (ren i)
  | lam t => lam (rename (ext ren) t)
  | app t1 t2 => app (rename ren t1) (rename ren t2)

def Subst (n1 n2 : Context) : Type := Var n1 → Term n2 

def exts {n1 n2} (sub : Subst n1 n2) : Subst (succ n1) (succ n2) :=
  fun x => match x with
           | Var.zero => var Var.zero
           | Var.succ x' => rename Var.succ (sub x')

def subst {n1 n2} (sub : Subst n1 n2) (t : Term n1) : Term n2 :=
  match t with
  | var i => sub i
  | lam t => lam (subst (exts sub) t)
  | app t1 t2 => app (subst sub t1) (subst sub t2)

def substZero {Γ} (t : Term Γ) : Subst (succ Γ) Γ :=
  fun x => match x with
           | Var.zero => t
           | Var.succ x' => var x'

def subLast {n} (t1 : Term (succ n)) (t2 : Term n) : Term n :=
  subst (substZero t2) t1

--------------------------------------------------------------------------------
---------- This section came from Subsitution.agda in plfa ---------------------
--------------------------------------------------------------------------------

-- The substitution alegra; all substitution can be built using these
def ids {Γ} : Subst Γ Γ := var

def shift {Γ} : Subst Γ (succ Γ) :=
  fun x => var (Var.succ x)

def cons {Γ Δ} (t : Term Δ) (sub : Subst Γ Δ) : Subst (succ Γ) Δ :=
  fun x => match x with
    | Var.zero => t
    | Var.succ x' => sub x'

def compose {n1 n2 n3} : Subst n1 n2 → Subst n2 n3 → Subst n1 n3 :=
  fun sub1 sub2 => subst sub2 ∘ sub1

def renToSub {Γ Δ} : Ren Γ Δ → Subst Γ Δ :=
  fun ren => ids ∘ ren

def bla : Nat → Nat := fun x => x 

theorem subIdL {Γ Δ} {sub : Subst Γ Δ} : compose ids sub = sub :=
  by apply funext
     intro x
     rfl
     

theorem subDist {n1 n2 n3} {sub1 : Subst n1 n2} {sub2 : Subst n2 n3} {M : Term n2}
  : (compose (cons M sub1) sub2) = (cons (subst sub2 M) (compose sub1 sub2)) :=
  by apply funext
     intro x
     cases x
     . rfl
     . rfl

theorem renExt {n1 n2} {ren : Ren n1 n2} : renToSub (ext ren) = exts (renToSub ren) := by
  apply funext
  intro x
  cases x
  . rfl
  . rfl


theorem renameSubstRen {n1 n2} {ren : Ren n1 n2} {M : Term n1}
  : rename ren M = subst (renToSub ren) M := by
  cases M
  . rfl
  . simp [rename, subst, renExt]; rw [(Eq.symm renExt)]; apply renameSubstRen
  . simp [subst, rename]
    apply And.intro
    . apply renameSubstRen
    . apply renameSubstRen

theorem extsConsShift {n1 n2} {sub : Subst n1 n2}
  : exts sub = cons (var Var.zero) (compose sub shift) := by
  apply funext
  intros x
  cases x
  . rfl
  . apply renameSubstRen

theorem substZConsIds {Γ} {M : Term Γ} : substZero M = (cons M ids) := by
  apply funext
  intro x
  cases x
  . rfl
  . rfl

theorem extsIds {Γ} : exts ids = @ids (succ Γ) := by
  apply funext
  intro x
  cases x
  . rfl
  . rfl

theorem subId {Γ} {M : Term Γ} : subst ids M = M := by
  induction M
  . rfl
  . simp [subst]
    rw [extsIds]
    assumption
  . simp [subst]
    apply And.intro
    . assumption
    . assumption

theorem renameId {Γ} {M : Term Γ} : rename (fun x => x) M = M := by
  rw [renameSubstRen]
  apply subId

theorem subIdR {Γ Δ} {sub : Subst Γ Δ} : (compose sub ids) = sub := by
  apply funext
  intro x
  apply subId

theorem composeExt {n1 n2 n3} {ren2 : Ren n2 n3} {ren1 : Ren n1 n2}
  : (ext ren2) ∘ (ext ren1) = ext (ren2 ∘ ren1) := by
  apply funext
  intro x
  cases x
  . rfl
  . rfl

theorem composeRename {n1} {M : Term n1} 
  : ∀ {n2 n3} {ren : Ren n2 n3} {ren' : Ren n1 n2},
    rename ren (rename ren' M) = rename (ren ∘ ren') M := by
  induction M with
  | var x => intros; rfl
  | lam t ih =>
    intros n2 n3 ren ren'
    simp [rename]
    rw [← composeExt]
    apply (@ih (succ n2) (succ n3) (ext ren) (ext ren'))
  | app t1 t2 ih1 ih2 =>
    intros
    simp [rename]
    apply And.intro
    . apply ih1
    . apply ih2

-- This is a helper used in commuteSubstRename, but seemingly lean has problems if I put its definition in there with the let tactic.
-- It seems that lean can't simp by locally defined definitions?
def ren' {ren : {Γ : Context} → Ren Γ (Nat.succ Γ)}
  : ∀{Γ}, Ren Γ (succ Γ) := fun {Γ} => match Γ with
  | Nat.zero => fun y => False.rec (noVarZero y)
  | Nat.succ _x' => ext ren

theorem commuteSubstRename {Γ} {M : Term Γ}
  : ∀ {Δ} {sub : Subst Γ Δ}
  {ren : ∀{Γ}, Ren Γ (succ Γ)},
   (r : ∀{x : Var Γ}, exts sub (ren x) = rename ren (sub x))
  → subst (exts sub) (rename ren M) = rename ren (subst sub M) := by
  induction M with
  | var x => intro Δ sub ren r; apply r
  | lam t ih =>
    intro Δ sub ren r
    simp [subst, rename]
    apply (@ih _ (exts sub) ren')
    simp [ren']
    intro x
    cases x with
    | zero => rfl
    | succ y =>
      simp [ext, exts]
      simp [exts] at r
      rw [r]
      simp [composeRename]
      rfl
  | app t1 t2 ih1 ih2 =>
    intro Δ sub ren r
    simp [subst, rename]
    apply And.intro
    . apply (ih1 r)
    . apply (ih2 r)

theorem extsSeq {Γ Δ Δ'} {sub1 : Subst Γ Δ} {sub2 : Subst Δ Δ'}
  : compose (exts sub1) (exts sub2) = exts (compose sub1 sub2) := by
  apply funext
  intro x
  cases x with
  | zero => rfl
  | succ y =>
    simp [compose]
    simp [exts]
    rw [<- commuteSubstRename]
    . rfl
    . intro x; rfl

theorem subSub {n1} {M : Term n1}
  : ∀ {n2 n3} {sub1 : Subst n1 n2} {sub2 : Subst n2 n3},
  subst sub2 (subst sub1 M) = subst (compose sub1 sub2) M := by
    induction M with
    | var i => intros; rfl
    | app t1 t2 ih1 ih2 =>
        intros
        simp [subst]
        apply And.intro
        apply ih1
        apply ih2
    | lam t ih =>
        intros
        --
        simp [subst]
        rw [ih]
        rw [extsSeq]

theorem renameSubst {Γ Δ Δ' : Context} {M : Term Γ} {ren : Ren Γ Δ} {sub : Subst Δ Δ'} 
  : subst sub (rename ren M) = subst (sub ∘ ren) M := by
  rw [renameSubstRen]
  simp [subSub]
  rfl

def bloo {n : Nat} : Nat := n

theorem subAssoc {n1 n2 n3 n4} {sub1 : Subst n1 n2} {sub2 : Subst n2 n3}
  {sub3 : Subst n3 n4}
  : compose (compose sub1 sub2) sub3 = compose sub1 (compose sub2 sub3) := by
  -- 
  apply funext
  intro x
  simp [compose]
  apply subSub

theorem subTail {n1 n2} {M : Term n2} {sub : Subst n1 n2}
  : compose shift (cons M sub) = sub := by
  apply funext
  intros x
  rfl

-- probably don't need this?
theorem renSuccShift {n}
  : renToSub (Var.succ) = @shift n := by
  -- apply funext
  -- intro x
  rfl

theorem substZeroSub {n1 n2} {M : Term n1} {sub : Subst n1 n2}
  : (compose (exts sub) (substZero (subst sub M))) = (compose (substZero M) sub) := by
    rw [extsConsShift]
    rw [substZConsIds]
    rw [substZConsIds]
    rw [subDist]
    rw [subDist]
    rw [subIdL]
    rw [subAssoc]
    rw [subTail]
    rw [subIdR]
    rfl

theorem substCommute {n1 n2} {N : Term (succ n1)} {M : Term n1} {sub : Subst n1 n2}
  : subLast (subst (exts sub) N) (subst sub M)
    = subst sub (subLast N M) := by
  simp [subLast]
  -- rw [extsConsShift]
  -- rw [substZConsIds]
  -- rw [substZConsIds]
  rw [subSub, subSub]
  rw [substZeroSub]

theorem renameSubstCommute {Γ Δ} {N : Term (succ Γ)} {M : Term Γ} {ren : Ren Γ Δ}
  : subLast (rename (ext ren) N) (rename ren M) = rename ren (subLast N M) := by
  rw [renameSubstRen]
  rw [renameSubstRen]
  rw [renameSubstRen]
  rw [renExt]
  rw [substCommute]

--------------------------------------------------------------------------------
---------- Stuff pertaining to relations in general ----------------------------
--------------------------------------------------------------------------------
-- from Nipkow (2001)

def Relation (A : Type) : Type 1 := A → A → Type

inductive Proof (P : Prop) : Type
| proof : P → Proof P

inductive TypeInhabited (P : Type n) : Prop
| elem : P → TypeInhabited P 

inductive DownLevel (T : Type 1) : Type 0 -- Hmmmm
| inhabited : Proof (TypeInhabited T) -> DownLevel T

-- -- reflexive closure of a relation
-- inductive reflClosure {A} (R : Relation A) : A → A → Type := _

-- transitive relflexive closure of a relation
inductive closure {A} (R : Relation A) : A → A → Type
| refl : ∀{a : A}, closure R a a
| cons : ∀{x y : A}, R x y → closure R y z  → closure R x z 

def oneStep {A} {R : Relation A} {x y : A} (step : R x y)
  : closure R x y := closure.cons step closure.refl

def transitivity {A} {R : Relation A} {x y z : A}
  (step1 : closure R x y) (step2 : closure R y z)
  : closure R x z :=
  match step1 with
  | closure.refl => step2
  | closure.cons s ss => closure.cons s (transitivity ss step2)

def liftCsr {A} {B} {R : Relation A} {R' : Relation B} {x y : A} (f : A → B)
  (ctr : ∀{x y}, R x y → R' (f x) (f y))
  : closure R x y → closure R' (f x) (f y) :=
  fun s => match s with
  | closure.refl => closure.refl
  | closure.cons xy yz => closure.cons (ctr xy) (liftCsr f ctr yz)

def square {A} (R S T U : Relation A) : Type :=
  {x y z : A} → R x y → S x z → Σ u, T y u × U z u

--     x --R-- y
--     |       |
--     S       T
--     |       |
--     z --U-- u

def prodIntro {A B} (a : A) (b : B) : A × B := ⟨a, b⟩

theorem stripLemma {A} {R S : Relation A}
  (sq : square R S (closure S) R) -- actually, can generalize to reflexive closure of R on output, but I don't need that for this development.
  : square R (closure S) (closure S) (closure R) :=
  fun {_x} {y} {z} Rxy Sxz => 
  match Sxz with
  | closure.refl => ⟨y, closure.refl, oneStep Rxy⟩ 
  | closure.cons xx' x'z =>
    let ⟨_out, s, r⟩ := sq Rxy xx'
    let ⟨out2, s2, r2⟩ := stripLemma sq r x'z
    ⟨out2, transitivity s s2, r2⟩ 

theorem commutationLemma {A} {R S : Relation A}
  (sq : square R S (closure S) R) -- actually, can generalize to reflexive closure of R on output, but I don't need that for this development.
  : square (closure R) (closure S) (closure S) (closure R) :=
  fun {_x} {y} {z} Rxy Sxz => 
  match Rxy with
  | closure.refl => ⟨z, Sxz, closure.refl⟩
  | closure.cons xx' x'z =>
    let ⟨_out, s, r⟩ := stripLemma sq xx' Sxz
    let ⟨out2, s2, r2⟩ := commutationLemma sq x'z s
    ⟨out2, s2, transitivity r r2⟩ 

--------------------------------------------------------------------------------
---------- The proof of confluence ---------------------------------------------
--------------------------------------------------------------------------------

def dummy : ∀{Γ}, Term Γ := lam (var Var.zero)

def renFree {Γ1 Γ2} (ren : Ren Γ1 Γ2) (t : Term Γ2) : Prop :=
  ∃ t', rename ren t' = t 

def subRenFree {Γ1 Γ Γ2} (ren : Ren Γ Γ2) (sub : Subst Γ1 Γ2) : Prop :=
  (x : Var Γ1) → renFree ren (sub x) 

def zFree {Γ} (t : Term (succ Γ)) : Prop := renFree Var.succ t

-- parallel beta-eta reduction
inductive Par : ∀{Γ}, Term Γ → Term Γ → Type   
| var : ∀{Γ} {x : Var Γ}, Par (var x) (var x)
| lam : ∀{Γ} {N N' : Term (succ Γ)},
  Par N N' → Par (lam N) (lam N')  
| app : ∀{Γ}{L L' M M' : Term Γ},
  Par L L' → Par M M' → Par (app L M) (app L' M')   
| beta : ∀{Γ}{N N' : Term (succ Γ)} {M M' : Term Γ},
  Par N N' → Par M M' → Par (app (lam N) M) (subLast N' M')  
| eta : ∀{Γ} {M M' : Term (succ Γ)},
  Par M M'
  → zFree M'
  → Par (lam (app M (var Var.zero))) (subLast M' dummy)

-- non-parallel beta-eta reduction
inductive Step : ∀{Γ}, Term Γ → Term Γ → Type where  
| app1 : ∀ {Γ} {L L' M : Term Γ},
    Step L L'
    → Step (app L M) (app L' M)
| app2 : ∀ {Γ} {L M M' : Term Γ},
    Step M M'
    → Step (app L M) (app L M')
| beta : ∀ {Γ} {N : Term (succ Γ)} {M : Term Γ},
    Step (app (lam N) M) (subLast N M)
| lam : ∀ {Γ} {N N' : Term (succ Γ)},
    Step N N' → Step (lam N) (lam N')
| eta : ∀{Γ} {N : Term (succ Γ)},
    zFree N
    → Step (lam (app N (var Var.zero))) (subLast N dummy)

theorem parRefl {Γ} {M : Term Γ} : Par M M := by
  induction M with
  | var i => apply Par.var
  | app t1 t2 ih1 ih2 => apply Par.app; apply ih1; apply ih2
  | lam t ih => apply Par.lam; apply ih

def RelSubst {n2} (R : Relation (Term n2)) {n1} (sub1 sub2 : Subst n1 n2) : Type :=
  {x : Var n1} → R (sub1 x) (sub2 x) 

def commutesSub (R : ∀{n}, Relation (Term n)) : Type :=
  ∀{Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ},
    (RelSubst R sub1 sub2) → (R M M')
    → R (subst sub1 M) (subst sub2 M')

-- I wrote this stuff to help with multiSubst, but is it necessary?
-- inductive MultiSubst {n1 n2} (R : Relation (Term n2)) : Subst n1 n2 → Subst n1 n2 → Type :=  
-- | refl : ∀{sub}, MultiSubst R sub sub 
-- | cons : ∀{sub1 sub2 sub3},
--   RelSubst R sub1 sub2 → MultiSubst R sub2 sub3 → MultiSubst R sub1 sub3 

-- theorem multiSubstToClosureSubst {n1 n2} (R : Relation (Term n2))
--   (sub1 sub2 : Subst n1 n2)
--   : (MultiSubst R sub1 sub2) → (RelSubst (closure R) sub1 sub2) :=
--   fun multiSubst {_x} => match multiSubst with
--   | MultiSubst.refl => closure.refl
--   | MultiSubst.cons r m => closure.cons r (multiSubstToClosureSubst _ _ _ m)

-- theorem subZeroEqual {n} (sub1 sub2 : Subst zero n) : sub1 = sub2 := by
--   apply funext
--   intro x
--   cases x

-- theorem closureSubstToMultiSubst {n1 n2} (R : Relation (Term n2))
--   (sub1 sub2 : Subst n1 n2)
--   : (RelSubst (closure R) sub1 sub2) → (MultiSubst R sub1 sub2) :=
--   match n1 with
--   | zero => by rw [subZeroEqual sub1 sub2]; intros; apply MultiSubst.refl
--   | Nat.succ n1' =>
--     let ih := closureSubstToMultiSubst R (fun {x} => sub1 (Var.succ x)) (fun {x} => sub2 (Var.succ x))
--     _

-- theorem multiSubst1 (R : ∀{n}, Relation (Term n))
--   (liftLam : ∀{n} {x y : Term (succ n)}, R x y → R (lam x) (lam y))
--   : commutesSub R
--   → 
--   ∀{Γ Δ} {sub1 sub2 : Subst Γ Δ} {M : Term Γ},
--     (RelSubst (closure R) sub1 sub2)
--     → closure R (subst sub1 M) (subst sub2 M)
--   := fun commutesR {Γ} {Δ} {sub1} {sub2} {M} rsub =>
--     match M with
--     | var i => @rsub i
--     | lam t =>
--       let bla := @multiSubst1 R liftLam commutesR (succ Γ) (succ Δ) (exts sub1) (exts sub2) t _ -- rsub
--       liftCsr lam liftLam bla
--     | app a b => _


-- theorem multiSubst (R : ∀{n}, Relation (Term n))
--   : commutesSub R → commutesSub (fun {n} => closure (@R n)) := by 
--   intro commutesR
--   simp [commutesSub]
--   intro Γ Δ sub1 sub2 M M' rsub rm
--   induction rm with
--   | refl => sorry
--   | cons => sorry


def ParSubst {Γ} {Δ} : (sub1 sub2 : Subst Γ Δ) → Type := RelSubst Par

theorem parRename {Γ} {M M' : Term Γ}
  (p : Par M M') 
  : ∀{Δ}, {ren : Ren Γ Δ} → Par (rename ren M) (rename ren M') := by
  induction p with
  | var => intros; simp [rename]; apply Par.var
  | lam _p ih => intros; simp [rename]; apply Par.lam; apply ih
  | app _p1 _p2 ih1 ih2 => intros; simp [rename]; apply Par.app; apply ih1; apply ih2
  | beta _p1 _p2 ih1 ih2 =>
    intros
    simp [rename]
    rw [<- renameSubstCommute]
    apply Par.beta
    apply ih1
    apply ih2
  | @eta _ M M' _p zf ih => -- TODO: surely this proof could be better....
    intro Δ ren
    simp [rename]
    rw [<- renameSubstCommute]
    apply Par.eta
    simp [zFree, renFree]
    apply ih
    apply Exists.elim; apply zf; intro t' eq
    exists (rename ren t')
    rw [composeRename]
    rw [<- eq]
    have lemma {n1 n2} {ren : Ren n1 n2} : ((ext ren) ∘ Var.succ) = Var.succ ∘ ren := by 
      apply funext
      intro x
      cases x
      . rfl
      . rfl
    rw [<- lemma]
    rw [composeRename]

theorem parSubstExts {Γ Δ} {sub1 sub2 : Subst Γ Δ}
  (ps : ParSubst sub1 sub2)
  : ParSubst (exts sub1) (exts sub2) := by
  intro x
  cases x
  . apply Par.var
  . apply parRename; apply ps

theorem substPar {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ}
  (ps : ParSubst sub1 sub2) (p : Par M M')
  : Par (subst sub1 M) (subst sub2 M') :=
  match p with
  | Par.var => ps
  | Par.app p1 p2 => Par.app (substPar ps p1) (substPar ps p2)
  | Par.beta p1 p2 => by
    rw [<- substCommute]
    apply Par.beta
    apply substPar
    apply parSubstExts
    apply ps
    apply p1
    apply substPar
    apply ps
    apply p2
  | Par.lam p => by
    apply Par.lam
    apply substPar
    apply parSubstExts
    apply ps
    apply p
  | Par.eta p zf => by
    simp [subst]
    simp [subLast]
    rw [subSub]
    rw [<- substZeroSub]
    rw [<- subSub]
    apply Par.eta
    apply substPar; apply parSubstExts; apply ps
    apply p
    simp [zFree, renFree] at *
    apply Exists.elim; apply zf; intro t' eq
    exists (subst sub2 t')
    rw [<- eq]
    rw [<- commuteSubstRename]
    intro x
    cases x
    . rfl
    . rfl

def parSubstZero {Γ} {M M' : Term Γ}
  (p : Par M M') : ParSubst (substZero M) (substZero M')
  := fun {x} =>
    match x with
    | Var.zero => p
    | Var.succ _x' => Par.var

theorem subPar {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : Par N N') (p2 : Par M M')
  : Par (subLast N M) (subLast N' M') :=
  substPar (parSubstZero p2) p1

theorem multiParSubstExts {Γ Δ} {sub1 sub2 : Subst Γ Δ}
  (ps : RelSubst (closure Par) sub1 sub2)
  : RelSubst (closure Par) (exts sub1) (exts sub2) := by
  intro x
  cases x with
  | zero =>  apply closure.refl
  | succ x' => simp [exts]; apply (liftCsr _ _ (@ps x')); intro _ _ p; apply parRename; apply p

theorem multiParSubst1 :
  ∀{Γ Δ} {sub1 sub2 : Subst Γ Δ} {M : Term Γ},
    (RelSubst (closure Par) sub1 sub2)
    → closure Par (subst sub1 M) (subst sub2 M)
  := fun {Γ} {Δ} {sub1} {sub2} {M} rsub =>
    match M with
    | var i => @rsub i
    | lam t =>
      let bla := @multiParSubst1 (succ Γ) (succ Δ) (exts sub1) (exts sub2) t (multiParSubstExts rsub)
      liftCsr lam Par.lam bla
    | app a b =>
      let bla1 := @multiParSubst1 Γ Δ sub1 sub2 a rsub
      let bla2 := @multiParSubst1 Γ Δ sub1 sub2 b rsub
      transitivity (liftCsr (fun x => app x _) (fun p => Par.app p parRefl) bla1)
      (liftCsr (app _) (fun p => Par.app parRefl p) bla2)

theorem multiParSubst
  : commutesSub (fun {n} => closure (@Par n)) := by 
  intro Γ Δ sub1 sub2 M M' rsub rm
  apply transitivity
  apply (multiParSubst1 rsub)
  induction rm with
  | refl => apply closure.refl
  | cons s _ss ih =>
    apply closure.cons
    apply substPar; apply (fun {x} => parRefl); apply s
    apply ih

theorem stepToPar {Γ} {t1 t2 : Term Γ}
  (step : Step t1 t2) : Par t1 t2 :=
  match step with
  | Step.app1 s => Par.app (stepToPar s) parRefl
  | Step.app2 s => Par.app parRefl (stepToPar s)
  | Step.lam s => Par.lam (stepToPar s)
  | Step.beta => Par.beta parRefl parRefl
  | Step.eta zf => Par.eta parRefl zf

theorem parToMultiStep {Γ} {t1 t2 : Term Γ}
  (par : Par t1 t2) : closure Step t1 t2 :=
  match par with
  | Par.var => closure.refl
  | Par.app p1 p2 => transitivity (liftCsr (fun x => app x _) Step.app1 (parToMultiStep p1))
    (liftCsr (app _) Step.app2 (parToMultiStep p2))
  | Par.lam s => liftCsr lam Step.lam (parToMultiStep s)
  | Par.beta s1 s2 => -- Can I do this case without proving substitution properties of MultiStep?
    transitivity (transitivity
      (liftCsr (fun x => app (lam x) _) (Step.app1 ∘ Step.lam) (parToMultiStep s1))
      (liftCsr (app _) Step.app2 (parToMultiStep s2)))
      (oneStep Step.beta)
  | Par.eta s zf =>
    transitivity
    (liftCsr (fun x => lam (app x _)) (Step.lam ∘ Step.app1) (parToMultiStep s))
    (oneStep (Step.eta zf))

theorem multiParToMultiStep {Γ} {t1 t2 : Term Γ}
  (par : closure Par t1 t2) : closure Step t1 t2 :=
  match par with
  | closure.refl => closure.refl
  | closure.cons s ss => transitivity (parToMultiStep s) (multiParToMultiStep ss)

theorem multiStepToMultiPar {Γ} {t1 t2 : Term Γ}
  (par : closure Step t1 t2) : closure Par t1 t2 :=
  match par with
  | closure.refl => closure.refl
  | closure.cons s ss => closure.cons (stepToPar s) (multiStepToMultiPar ss)

theorem multiStepSubst
  : commutesSub (fun {n} => closure (@Step n)) :=
    fun rSub rM => multiParToMultiStep (multiParSubst
      (fun {x} => multiStepToMultiPar (@rSub x))
      (multiStepToMultiPar rM))

def multiStepSubstZero {Γ} {M M' : Term Γ}
  (p : closure Step M M') : RelSubst (closure Step) (substZero M) (substZero M')
  := fun {x} =>
    match x with
    | Var.zero => p
    | Var.succ _x' => closure.refl

theorem subMultiStep {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : closure Step N N') (p2 : closure Step M M')
  : closure Step (subLast N M) (subLast N' M') :=
  multiStepSubst (multiStepSubstZero p2) p1

------------------------------- Some theorems related to zFree

theorem lamRenFree {n2} {M : Term (succ n2)} {ren : Ren n1 n2}
  : renFree (ext ren) M ↔ renFree ren (lam M) :=
    Iff.intro
      (fun ⟨t, renProof⟩ => ⟨lam t, by simp [rename]; apply renProof⟩)
      (fun ⟨lam t, renProof⟩ => ⟨ t, by simp [rename] at renProof; apply renProof⟩)

theorem appRenFree {n2} {M N : Term n2} {ren : Ren n1 n2}
  : (renFree ren M /\ renFree ren N) ↔ renFree ren (app M N) :=
    Iff.intro
      (fun ⟨⟨t1, p1⟩, ⟨t2, p2⟩⟩ => ⟨app t1 t2, by simp [rename]; apply And.intro; apply p1; apply p2⟩)
      (fun ⟨app t1 t2, p⟩ =>
        ⟨⟨t1, by simp [rename] at p; apply (And.left p)⟩
        , ⟨t2, by simp [rename] at p; apply (And.right p)⟩⟩)

theorem subLastZFree {n} {M : Term (succ n)} {d1 d2 : Term n}
  (zf : zFree M)
  : subLast M d1 = subLast M d2 := by
  simp [zFree, renFree] at zf
  apply Exists.elim; apply zf; intro t' eq
  rw [<- eq]
  have lemma {n} {a b : Term n} : subLast (rename Var.succ a) b = a := by
      rw [renameSubstRen]
      simp [subLast]
      rw [substZConsIds]
      rw [subSub]
      have lemma' : compose (renToSub Var.succ) (cons b ids) = ids := by
        apply funext
        intro x
        cases x
        . rfl
        . rfl
      rw [lemma']
      rw [subId]
  rw [lemma]
  rw [lemma]

-- def subRenFree {Γ1 Γ Γ2} (ren : Ren Γ Γ2) (sub : Subst Γ1 Γ2) : Prop :=
--   (x : Var Γ1) → renFree ren (sub x) 

theorem substRenFree {Γ1 Γ Γ2} (ren : Ren Γ Γ1) (sub : Subst Γ1 Γ2)
  (srf : subRenFree ren sub) (M : Term Γ1)
  : renFree ren M → renFree ren (subst sub M) := by sorry

theorem stepZFree {n1 n2} {M N : Term n2} (step : Step M N) {ren : Ren n1 n2}
  (rf : renFree ren M) : renFree ren N :=
  match step with
  | Step.app1 p => Iff.mp appRenFree
    ⟨stepZFree p (And.left (Iff.mpr appRenFree rf))
    , And.right (Iff.mpr appRenFree rf)⟩  
  | Step.app2 p => Iff.mp appRenFree
    ⟨And.left (Iff.mpr appRenFree rf)
    , stepZFree p (And.right (Iff.mpr appRenFree rf))⟩  
  | Step.lam p => Iff.mp lamRenFree (stepZFree p (Iff.mpr lamRenFree rf))
  | Step.beta => _
  | Step.eta zf => _
    -- let M'zf := stepZFree p zf
    -- let thing1 := stepZFree p (And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf)))
    -- let thing2 := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
    -- let ⟨t, proof⟩ := stepZFree p (And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf)))
    -- let ⟨t', proof'⟩ := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
    -- ⟨subLast t dummy, (by 
    --   rw [<- renameSubstCommute]
    --   rw [<- proof]
    --   -- rfl
    --   sorry
    --   ) ⟩

theorem stepBackZFree {n1 n2} {M N : Term n2} (step : Step N M) {ren : Ren n1 n2}
  (rf : renFree ren M) : renFree ren N := by sorry

-- theorem parZFree {n1 n2} {M N : Term n2} (step : Par M N) {ren : Ren n1 n2}
--   (rf : renFree ren M) : renFree ren N :=
--   match step with
--   | Par.var => rf
--   | Par.app p1 p2 => Iff.mp appRenFree
--     ⟨parZFree p1 (And.left (Iff.mpr appRenFree rf))
--     , parZFree p2 (And.right (Iff.mpr appRenFree rf))⟩  
--   | Par.lam p => Iff.mp lamRenFree (parZFree p (Iff.mpr lamRenFree rf))
--   | Par.beta p1 p2 => _
--   | Par.eta p zf =>
--     let M'zf := parZFree p zf
--     let thing1 := parZFree p (And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf)))
--     let thing2 := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
--     let ⟨t, proof⟩ := parZFree p (And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf)))
--     let ⟨t', proof'⟩ := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
--     ⟨subLast t dummy, (by 
--       rw [<- renameSubstCommute]
--       rw [<- proof]
--       -- rfl
--       sorry
--       ) ⟩




-- square Par Step Step* Par -> square Par* Step* Step* Par*
theorem commutationProperty {Γ}
  : square (@Par Γ) (@Step Γ) (closure (@Step Γ)) (@Par Γ) :=
  fun {x} {y} {z} p1 p2 =>
  match p1, p2 with
  | Par.app a1 b1, Step.app1 a2 =>
    let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
    ⟨app a _, liftCsr (fun x => app x _) Step.app1 pa1, Par.app pa2 b1⟩
  | Par.app a1 b1, Step.app2 b2 =>
    let ⟨b, pb1, pb2⟩ := commutationProperty b1 b2
    ⟨app _ b, liftCsr (app _) Step.app2 pb1, Par.app a1 pb2⟩
  | Par.beta a1 b1, Step.beta =>
    ⟨_, closure.refl, subPar a1 b1⟩
  | Par.beta a1 b1, Step.app2 b2 =>
    let ⟨_, c, d⟩ := commutationProperty b1 b2
    ⟨_, subMultiStep closure.refl c,
      Par.beta a1 d⟩
  | Par.app (Par.lam a1) b1, Step.beta =>
    ⟨_, closure.cons Step.beta closure.refl, subPar a1 b1⟩ 
  | Par.beta a1 b1, Step.app1 (Step.lam a2) =>
    let ⟨_, c, d⟩ := commutationProperty a1 a2
    ⟨_, subMultiStep c closure.refl, Par.beta d b1⟩
  | Par.app (Par.eta a1 zf) b1, Step.beta =>
    ⟨_, closure.refl, Par.app (by
      rw [subLastZFree]
      apply subPar
      apply a1
      apply b1
      apply zf
      ) b1⟩ -- requires zFree lemma
  | Par.beta a1 b1, Step.app1 (Step.eta zf) => -- splits into two cases
    by
    cases a1 with
    | app p var => exact (
      ⟨_, _, Par.app (subPar p parRefl) parRefl⟩)
    | beta p var => sorry
  | Par.lam a1, Step.lam a2 =>
    let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
    ⟨lam a, liftCsr lam Step.lam pa1, Par.lam pa2⟩
  | Par.lam a, Step.eta zf => _ -- splits into two cases
  | Par.eta zf t1, Step.lam t2 => _ -- splits into three cases on t2 (although one trivially is impossible)
  | Par.eta a1 zf, Step.eta zf2 =>
    ⟨_, closure.refl, subPar a1 parRefl⟩

-- TODO:
-- https://drops.dagstuhl.de/opus/volltexte/2019/11406/pdf/LIPIcs-TYPES-2018-2.pdf

theorem confluence1 {Γ}
  : square (closure (@Par Γ)) (closure (@Step Γ)) (closure (@Step Γ)) (closure (@Par Γ)) :=
    commutationLemma commutationProperty

theorem commutationProperty3 {Γ}
  : square (@Par Γ) (@Step Γ) (closure (@Step Γ)) (@Par Γ) :=
  fun {x} {y} {z} p1 p2 =>
  match p1, p2 with
  | Par.app a1 b1, Step.app1 a2 =>
    let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
    ⟨app a _, liftCsr (fun x => app x _) Step.app1 pa1, Par.app pa2 b1⟩
  | Par.app a1 b1, Step.app2 b2 =>
    let ⟨b, pb1, pb2⟩ := commutationProperty b1 b2
    ⟨app _ b, liftCsr (app _) Step.app2 pb1, Par.app a1 pb2⟩
  | Par.beta a1 b1, Step.beta =>
    ⟨_, closure.refl, subPar a1 b1⟩
  | Par.beta a1 b1, Step.app2 b2 =>
    let ⟨_, c, d⟩ := commutationProperty b1 b2
    ⟨_, subMultiStep closure.refl c,
      Par.beta a1 d⟩
  | Par.app (Par.lam a1) b1, Step.beta =>
    ⟨_, closure.cons Step.beta closure.refl, subPar a1 b1⟩ 
  | Par.beta a1 b1, Step.app1 (Step.lam a2) =>
    let ⟨_, c, d⟩ := commutationProperty a1 a2
    ⟨_, subMultiStep c closure.refl, Par.beta d b1⟩
  | Par.app (Par.eta a1 zf) b1, Step.beta =>
    ⟨_, closure.refl, Par.app (by
      rw [subLastZFree]
      apply subPar
      apply a1
      apply b1
      apply zf
      ) b1⟩ -- requires zFree lemma
  | Par.beta a1 b1, Step.app1 (Step.eta zf) => -- splits into two cases
    match x, a1 with
    | app (lam (app t1 (var Var.zero))) t2, (Par.app a1 Par.var) => _
    | app (lam (app (lam t1) (var Var.zero))) t2, Par.beta a1 Par.var => _
  | Par.lam a1, Step.lam a2 =>
    let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
    ⟨lam a, liftCsr lam Step.lam pa1, Par.lam pa2⟩
  | Par.lam a, Step.eta zf => _ -- splits into two cases
  | Par.eta zf t1, Step.lam t2 => _ -- splits into three cases on t2 (although one trivially is impossible)
  | Par.eta a1 zf, Step.eta zf2 =>
    ⟨_, closure.refl, subPar a1 parRefl⟩

-- theorem commutationProperty2 {Γ}
--   : square (@Par Γ) (@Step Γ) (closure (@Step Γ)) (@Par Γ) :=
--   fun {x} {y} {z} p1 p2 =>
--   match x, y, z, p1, p2 with
--   | app t1 t2, .(_), .(_), Par.app a1 b1, Step.app1 a2 =>
--     let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
--     ⟨app a _, liftCsr (fun x => app x _) Step.app1 pa1, Par.app pa2 b1⟩
--   | app t1 t2, .(_), .(_), Par.app a1 b1, Step.app2 b2 =>
--     let ⟨b, pb1, pb2⟩ := commutationProperty b1 b2
--     ⟨app _ b, liftCsr (app _) Step.app2 pb1, Par.app a1 pb2⟩
--   | app (lam t1) t2, .(_), .(_), Par.beta a1 b1, Step.beta =>
--     ⟨_, closure.refl, subPar a1 b1⟩
--   | app (lam t1) t2, .(_), .(_), Par.beta a1 b1, Step.app2 b2 =>
--     let ⟨_, c, d⟩ := commutationProperty b1 b2
--     ⟨_, subMultiStep closure.refl c,
--       Par.beta a1 d⟩
--   | app (lam t1) t2, .(_), .(_), Par.app (Par.lam a1) b1, Step.beta =>
--     ⟨_, closure.cons Step.beta closure.refl, subPar a1 b1⟩ 
--   | app (lam t1) t2, .(_), .(_), Par.beta a1 b1, Step.app1 (Step.lam a2) =>
--     let ⟨_, c, d⟩ := commutationProperty a1 a2
--     ⟨_, subMultiStep c closure.refl, Par.beta d b1⟩
--   | .(_), .(_), .(_), Par.app (Par.eta a1 zf) b1, Step.beta =>
--     ⟨_, closure.refl, Par.app (by
--       rw [subLastZFree]
--       apply subPar
--       apply a1
--       apply b1
--       apply zf
--       ) b1⟩ -- requires zFree lemma
--   -- | .(_), .(_), .(_), Par.beta a1 b1, Step.app1 (Step.eta zf) => _ -- splits into two cases
--   | app (lam (app t1 (var Var.zero))) t2, .(_), .(_), Par.beta (Par.app a1 Par.var) b1, Step.app1 (Step.eta zf) => _ -- splits into two cases
--   | app (lam (app (lam t1) (var Var.zero))) t2, .(_), .(_), Par.beta (Par.beta a1 Par.var) b1, Step.app1 (Step.eta zf) => _ -- splits into two cases
--   | .(_), .(_), .(_), Par.lam a1, Step.lam a2 =>
--     let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
--     ⟨lam a, liftCsr lam Step.lam pa1, Par.lam pa2⟩
--   | .(_), .(_), .(_), Par.lam a, Step.eta zf => _ -- splits into two cases
--   | .(_), .(_), .(_), Par.eta zf t1, Step.lam t2 => _ -- splits into three cases on t2 (although one trivially is impossible)
--   | .(_), .(_), .(_), Par.eta a1 zf, Step.eta zf2 =>
--     ⟨_, closure.refl, subPar a1 parRefl⟩
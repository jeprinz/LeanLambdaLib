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
-- | eta : ∀{Γ} {M M' : Term Γ},
--   Par M M'
--   → Par (lam (app (rename Var.succ M) (var Var.zero))) M'
| eta : ∀{Γ} {M M' : Term (succ Γ)},
  Par M M'
→ zFree M
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

def ParSubst {Γ} {Δ} (sub1 sub2 : Subst Γ Δ) : Type :=
  {x : Var Γ} →Par (sub1 x) (sub2 x)

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
    have eq' : rename ((ext ren) ∘ Var.succ) t' = rename (ext ren) M := by
      rw [<- composeRename]
      apply congrArg
      apply eq
    have lemma {n1 n2} {ren : Ren n1 n2} : ((ext ren) ∘ Var.succ) = Var.succ ∘ ren := by 
      apply funext
      intro x
      cases x
      . rfl
      . rfl
    rw [<- lemma]
    apply eq'

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
    exists (subst sub1 t')
    have eq' : subst (exts sub1) (rename (Var.succ) t') = subst (exts sub1) _ := by -- _ is M✝
      apply congrArg
      apply eq
    rw [<- commuteSubstRename]
    apply eq'
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
    (oneStep (Step.eta _))
    -- transitivity
    --   (oneStep (Step.eta zf))
    --   _

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

theorem parZFree {n1 n2} {M N : Term n2} (step : Par M N) {ren : Ren n1 n2}
  (rf : renFree ren M) : renFree ren N :=
  match step with
  | Par.var => rf
  | Par.app p1 p2 => Iff.mp appRenFree
    ⟨parZFree p1 (And.left (Iff.mpr appRenFree rf))
    , parZFree p2 (And.right (Iff.mpr appRenFree rf))⟩  
  | Par.lam p => Iff.mp lamRenFree (parZFree p (Iff.mpr lamRenFree rf))
  | Par.beta p1 p2 => _
  | Par.eta p zf =>
    let M'zf := parZFree p zf
    let thing1 := parZFree p (And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf)))
    let thing2 := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
    let ⟨t, proof⟩ := parZFree p (And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf)))
    let ⟨t', proof'⟩ := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
    ⟨subLast t dummy, (by 
      rw [<- renameSubstCommute]
      rw [<- proof]
      -- rfl
      sorry
      ) ⟩




-- square Par Step Step* Par -> square Par* Step* Step* Par*
theorem commutationProperty {Γ}
  : square (@Par Γ) (@Step Γ) (closure (@Step Γ)) (@Par Γ) :=
  fun p1 p2 =>
  match p1, p2 with
  | Par.app a1 b1, Step.app1 a2 =>
    let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
    ⟨app a _, liftCsr (fun x => app x _) Step.app1 pa1, Par.app pa2 b1⟩
  | Par.app a1 b1, Step.app2 b2 =>
    let ⟨b, pb1, pb2⟩ := commutationProperty b1 b2
    ⟨app _ b, liftCsr (app _) Step.app2 pb1, Par.app a1 pb2⟩
  | Par.beta a1 b1, Step.beta => _
  | Par.beta a1 b1, Step.app2 b2 => _
  | Par.app (Par.lam a1) b1, Step.beta => _
  | Par.beta a1 b1, Step.app1 (Step.lam a2) => _
  | Par.app (Par.eta zf a1) b1, Step.beta => _
  | Par.beta a1 b1, Step.app1 (Step.eta zf) => _
  | Par.lam a1, Step.lam a2 =>
    let ⟨a, pa1, pa2⟩ := commutationProperty a1 a2
    ⟨lam a, _, _⟩
  | Par.lam a1, Step.eta zf => _
  | Par.eta zf t1, Step.lam t2 => _
  | Par.eta zf a1, Step.eta zf2 => _
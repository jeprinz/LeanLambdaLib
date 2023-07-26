-- This file is a translation of PLFA

-- https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html

--------------------------------------------------------------------------------
---------- This section came from Untyped.agda in plfa -------------------------
--------------------------------------------------------------------------------


open Fin
open Option

inductive Context : Type
| zero : Context
| succ : Context → Context 
open Context

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

mutual
  inductive Neutral : ∀{Γ}, Term Γ → Type  
  | var : ∀{Γ}, (x : Var Γ) → Neutral (var x) 
  | app : ∀{Γ}, {t1 t2 : Term Γ} → Neutral t1 → Normal t2 → Neutral (app t1 t2) 

  inductive Normal : ∀{Γ}, Term Γ → Type  
  | neu : ∀{Γ}, {t : Term Γ} → Neutral t → Normal t 
  | lam : ∀{Γ}, {t : Term (succ Γ)} → Normal t → Normal (lam t) 
end

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

-- | eta : ∀{Γ} {N : Term Γ},
--     Step (lam (app (rename Var.succ N) (var Var.zero))) N

-- infix:50 " ==> " => Step

inductive MultiStep : ∀ {Γ}, Term Γ → Term Γ → Type
| halt : ∀ {Γ} {t : Term Γ}, MultiStep t t
| step : ∀ {Γ} {t1 t2 t3 : Term Γ},
  Step t1 t2 → MultiStep t2 t3 → MultiStep t1 t3  

def progress {Γ} (M : Term Γ)
  : (Σ N, Step M N) ⊕ (Normal M)
  := match M with
     | (var x) => Sum.inr (Normal.neu (Neutral.var x))
     | lam N => match progress N with
                | Sum.inl ⟨_ , s⟩ => Sum.inl ⟨_ , Step.lam s⟩ 
                | Sum.inr t => Sum.inr (Normal.lam t)
     | (app (lam _) _) => Sum.inl ⟨_ , Step.beta⟩
     | (app (var x) M) => match progress M with
              | Sum.inl ⟨_ , s⟩ => Sum.inl ⟨_ , Step.app2 s⟩
              | Sum.inr normN => Sum.inr (Normal.neu (Neutral.app (Neutral.var x) normN))
     | (app (app a b) M) => match progress (app a b) with
              | Sum.inl ⟨_ , s⟩ => Sum.inl ⟨_ , Step.app1 s⟩ 
              | Sum.inr (Normal.neu normN) => match progress M with
                    | Sum.inl ⟨_ , s⟩ => Sum.inl  ⟨_ , Step.app2 s⟩ 
                    | Sum.inr normM => Sum.inr (Normal.neu (Neutral.app normN normM))

def eval {Γ} (fuel : Nat) (t1 : Term Γ)
  : Option (Σ t2, ((MultiStep t1 t2) × (Normal t2))) :=
  match fuel with
  | Nat.zero => none
  | Nat.succ fuel' => match progress t1 with
    | Sum.inl ⟨t' , s⟩ => do 
        let ⟨final , steps , nf⟩ <- eval fuel' t'
        some ⟨final , MultiStep.step s steps , nf⟩
    | Sum.inr norm => some ⟨t1 , MultiStep.halt , norm⟩

-- infix:50 " ~>> " => MultiStep
-- infix:50 " ~>> " => MultiStep

def multiTrans {Γ} {L M N : Term Γ}
  (s1 : MultiStep L M) (s2 : MultiStep M N) : MultiStep L N :=
  match s1 with
  | MultiStep.halt => s2
  | MultiStep.step s steps => MultiStep.step s (multiTrans steps s2)

def appLCong {Γ} {L L' M : Term Γ}
  (m : MultiStep L L') : MultiStep (app L M) (app L' M) :=
  match m with
  | MultiStep.halt => MultiStep.halt
  | MultiStep.step s steps => MultiStep.step (Step.app1 s) (appLCong steps)

def appRCong {Γ} {L M M' : Term Γ}
  (m : MultiStep M M') : MultiStep (app L M) (app L M') :=
  match m with
  | MultiStep.halt => MultiStep.halt
  | MultiStep.step s steps => MultiStep.step (Step.app2 s) (appRCong steps)

def appCong {n} {L L' M M' : Term n}
  (m1 : MultiStep L L') (m2 : MultiStep M M') : MultiStep (app L M) (app L' M') :=
  multiTrans (appLCong m1) (appRCong m2)

def lamCong {Γ} {M M' : Term (succ Γ)}
  (m : MultiStep M M') : MultiStep (lam M) (lam M') :=
  match m with
  | MultiStep.halt => MultiStep.halt
  | MultiStep.step s steps => MultiStep.step (Step.lam s) (lamCong steps)

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
def ren' {ren : {Γ : Context} → Ren Γ (Context.succ Γ)}
  : ∀{Γ}, Ren Γ (succ Γ) := fun {Γ} => match Γ with
  | Context.zero => fun y => False.rec (noVarZero y)
  | Context.succ _x' => ext ren

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
---------- A proof of confluence -----------------------------------------------
--------------------------------------------------------------------------------

inductive Par : ∀{Γ}, Term Γ → Term Γ → Type   
| pvar : ∀{Γ} {x : Var Γ}, Par (var x) (var x)
| plam : ∀{Γ} {N N' : Term (succ Γ)},
  Par N N' → Par (lam N) (lam N')  
| papp : ∀{Γ}{L L' M M' : Term Γ},
  Par L L' → Par M M' → Par (app L M) (app L' M')   
| pbeta : ∀{Γ}{N N' : Term (succ Γ)} {M M' : Term Γ},
  Par N N' → Par M M' → Par (app (lam N) M) (subLast N' M')  

def ParSubst {Γ} {Δ} (sub1 sub2 : Subst Γ Δ) : Type :=
  {x : Var Γ} → Par (sub1 x) (sub2 x)

theorem parRename {Γ} {M M' : Term Γ}
  (p : Par M M') 
  : ∀{Δ}, {ren : Ren Γ Δ} → Par (rename ren M) (rename ren M') := by
  induction p with
  | pvar => intros; simp [rename]; apply Par.pvar
  | plam _p ih => intros; simp [rename]; apply Par.plam; apply ih
  | papp _p1 _p2 ih1 ih2 => intros; simp [rename]; apply Par.papp; apply ih1; apply ih2
  | pbeta _p1 _p2 ih1 ih2 =>
    intros
    simp [rename]
    rw [<- renameSubstCommute]
    apply Par.pbeta
    apply ih1
    apply ih2

theorem parSubstExts {Γ Δ} {sub1 sub2 : Subst Γ Δ}
  (ps : ParSubst sub1 sub2)
  : ParSubst (exts sub1) (exts sub2) := by
  intro x
  cases x
  . apply Par.pvar
  . apply parRename; apply ps

theorem substPar {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ}
  (ps : ParSubst sub1 sub2) (p : Par M M')
  : Par (subst sub1 M) (subst sub2 M') :=
  match p with
  | Par.pvar => ps
  | Par.papp p1 p2 => Par.papp (substPar ps p1) (substPar ps p2)
  | Par.pbeta p1 p2 => by
    rw [<- substCommute]
    apply Par.pbeta
    apply substPar
    apply parSubstExts
    apply ps
    apply p1
    apply substPar
    apply ps
    apply p2
  | Par.plam p => by
    apply Par.plam
    apply substPar
    apply parSubstExts
    apply ps
    apply p

def parSubstZero {Γ} {M M' : Term Γ}
  (p : Par M M') : ParSubst (substZero M) (substZero M')
  := fun {x} =>
    match x with
    | Var.zero => p
    | Var.succ _x' => Par.pvar

theorem subPar {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : Par N N') (p2 : Par M M')
  : Par (subLast N M) (subLast N' M') :=
  substPar (parSubstZero p2) p1

theorem parRefl {Γ} {M : Term Γ} : Par M M := by
  induction M with
  | var i => apply Par.pvar
  | app t1 t2 ih1 ih2 => apply Par.papp; apply ih1; apply ih2
  | lam t ih => apply Par.plam; apply ih

-- While on paper the Takahashi method leads to a cleaner proof, in a theorem prover the proof
-- will be ugly either way and this way is shorter.
-- Also, using a takahashi function for beta-eta together seems to be very difficuly formally,
-- since the eta rule involves a substiution
theorem parDiamond {Γ} {t t1 t2 : Term Γ}
  (p1 : Par t t1) (p2 : Par t t2)
  : Σ t', Par t1 t' × Par t2 t' :=
  match p1, p2 with
  | Par.pvar, Par.pvar => ⟨_, Par.pvar, Par.pvar⟩
  | Par.papp a1 b1, Par.papp a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨app a b, Par.papp pa1 pb1, Par.papp pa2 pb2⟩
  | Par.pbeta a1 b1, Par.pbeta a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subLast a b, subPar pa1 pb1, subPar pa2 pb2⟩
  | Par.papp (Par.plam a1) b1, Par.pbeta a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subLast a b, Par.pbeta pa1 pb1, subPar pa2 pb2⟩
  | Par.pbeta a1 b1, Par.papp (Par.plam a2) b2 => -- REPEATED CASE
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subLast a b, subPar pa1 pb1, Par.pbeta pa2 pb2⟩
  | Par.plam a1, Par.plam a2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    ⟨lam a, Par.plam pa1, Par.plam pa2⟩

-------- Relations - from Nipkow (2001)
def Relation (A : Type) : Type 1 := A → A → Type

inductive Proof (P : Prop) : Type
| proof : P → Proof P

def closeRef {A} (R : Relation A) : Relation A :=
  fun x y => (Proof (x = y)) ⊕ R x y

def liftRef {A} {B} {R : Relation A} {R' : Relation B} {x y : A} (f : A → B)
  (ctr : ∀{x y}, R x y → R' (f x) (f y))
  : closeRef R x y → closeRef R' (f x) (f y) :=
  fun s => match s with 
  | Sum.inl (Proof.proof rfl) => Sum.inl (Proof.proof rfl)
  | Sum.inr s' => Sum.inr (ctr s')

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

inductive union {A} (R S : Relation A) : A → A → Type  
| r : ∀{x y}, R x y → union R S x y 
| s : ∀{x y}, S x y → union R S x y

def leftClosureUnion {A x y} {R S : Relation A}
  (r : closure R x y) : closure (union R S) x y :=
  match r with
  | closure.refl => closure.refl
  | closure.cons s ss => closure.cons (union.r s) (leftClosureUnion ss)

def rightClosureUnion {A x y} {R S : Relation A}
  (s : closure S x y) : closure (union R S) x y :=
  match s with
  | closure.refl => closure.refl
  | closure.cons s ss => closure.cons (union.s s) (rightClosureUnion ss)

def oneUnionStep {A x y} {R S : Relation A}
  (s : union R S x y) : union (closure R) (closure S) x y :=
  match s with
  | union.r r => union.r (oneStep r)
  | union.s s => union.s (oneStep s)

def unionClosureToClosureUnion {A x y} {R S : Relation A}
  (s : union (closure R) (closure S) x y) : closure (union R S) x y :=
  match s with
  | union.r r => leftClosureUnion r
  | union.s s => rightClosureUnion s

-- All from Nipkow paper
def square {A} (R S T U : Relation A) : Type :=
  {x y z : A} → R x y → S x z → Σ u, T y u × U z u

def commute {A} (R S : Relation A) : Type := square R S S R
def diamond {A} (R : Relation A) : Type := commute R R
def confluent {A} (R : Relation A) : Type := diamond (closure R)

--     x --R-- y
--     |       |
--     S       T
--     |       |
--     z --U-- u

theorem stripLemma {A} {R S : Relation A}
  (sq : square R S (closure S) (closeRef R))
  : square R (closure S) (closure S) (closure R) :=
  fun {_x} {y} {z} Rxy Sxz => 
  match Sxz with
  | closure.refl => ⟨y, closure.refl, oneStep Rxy⟩ 
  | closure.cons xx' x'z =>
    let ⟨out, s, r⟩ := sq Rxy xx'
    match r with
    | Sum.inl (Proof.proof p) =>
      ⟨z, transitivity s (by rw [<- p]; exact x'z), closure.refl⟩ 
    | Sum.inr r' =>
      let ⟨out2, s2, r2⟩ := stripLemma sq r' x'z
      ⟨out2, transitivity s s2, r2⟩

theorem commutationLemma {A} {R S : Relation A}
  (sq : square R S (closure S) (closeRef R))
  : square (closure R) (closure S) (closure S) (closure R) :=
  fun {_x} {y} {z} Rxy Sxz => 
  match Rxy with
  | closure.refl => ⟨z, Sxz, closure.refl⟩
  | closure.cons xx' x'z =>
    let ⟨_out, s, r⟩ := stripLemma sq xx' Sxz
    let ⟨out2, s2, r2⟩ := commutationLemma sq x'z s
    ⟨out2, s2, transitivity r r2⟩ 

theorem commutativeUnion {A} {R S : Relation A}
  (rConfluent : confluent R) (sConfluent : confluent S)
  (commutes : commute (closure R) (closure S)) : confluent (union R S) :=
  fun {x} {y} {z} =>
  let rec commutativeUnionLemma
    : square (union (closure R) (closure S)) (closure (union R S))
      (closure (union R S)) (union (closure R) (closure S)) :=
    fun {x} {y} {z} top left =>
      match left with
      | closure.refl => ⟨y, closure.refl, top⟩
      | closure.cons s ss =>
        match s, top with
        | union.r left', union.r top' =>
          let ⟨w', right', top''⟩ := rConfluent top' (oneStep left')
          let ⟨w, right, bottom⟩ := commutativeUnionLemma (union.r top'') ss
          ⟨w, transitivity (leftClosureUnion right') right, bottom⟩
        | union.r left', union.s top' =>
          let ⟨w', top'', right'⟩ := commutes (oneStep left') top'
          let ⟨w, right, bottom⟩ := commutativeUnionLemma (union.s top'') ss
          ⟨w, transitivity (leftClosureUnion right') right, bottom⟩
        | union.s left', union.r top' =>
          let ⟨w', right', top''⟩ := commutes top' (oneStep left')
          let ⟨w, right, bottom⟩ := commutativeUnionLemma (union.r top'') ss
          ⟨w, transitivity (rightClosureUnion right') right, bottom⟩
        | union.s left', union.s top' =>
          let ⟨w', right', top''⟩ := sConfluent top' (oneStep left')
          let ⟨w, right, bottom⟩ := commutativeUnionLemma (union.s top'') ss
          ⟨w, transitivity (rightClosureUnion right') right, bottom⟩
    by
      intro top
      revert z
      induction top with
      | refl => intro z left; exact ⟨_, left, closure.refl⟩
      | cons s _ss ih =>
        intro z left
        let ⟨_, right', bottom'⟩ := commutativeUnionLemma (oneUnionStep s) left 
        let ⟨out2, right, bottom⟩ := ih right'
        exact ⟨out2, right, transitivity (unionClosureToClosureUnion bottom') bottom⟩ 


------- Eta ----------------------------------------------------------------------------------------------

def dummy : ∀{Γ}, Term Γ := lam (var Var.zero)

def renFree {Γ1 Γ2} (ren : Ren Γ1 Γ2) (t : Term Γ2) : Prop :=
  ∃ t', rename ren t' = t 

def zFree {Γ} (t : Term (succ Γ)) : Prop := renFree Var.succ t

inductive StepEta : ∀{Γ}, Term Γ → Term Γ → Type where  
| app1 : ∀ {Γ} {L L' M : Term Γ},
    StepEta L L'
    → StepEta (app L M) (app L' M)
| app2 : ∀ {Γ} {L M M' : Term Γ},
    StepEta M M'
    → StepEta (app L M) (app L M')
| lam : ∀ {Γ} {N N' : Term (succ Γ)},
    StepEta N N' → StepEta (lam N) (lam N')
| eta : ∀{Γ} {M : Term (succ Γ)},
 -- The idea to use subsitution here is from Nipkow 2001
  zFree M
  → StepEta (lam (app M (var Var.zero))) (subLast M dummy)

theorem etaRename {Γ} {M M' : Term Γ}
  (p : StepEta M M') 
  : ∀{Δ}, {ren : Ren Γ Δ} → StepEta (rename ren M) (rename ren M') := by
  induction p with
  | lam _p ih => intros; simp [rename]; apply StepEta.lam; apply ih
  | app1 _p ih => intros; simp [rename]; apply StepEta.app1; apply ih
  | app2 _p ih => intros; simp [rename]; apply StepEta.app2; apply ih
  | @eta _ M zf => -- surely I could have written this proof better...
    intro Δ ren
    simp [rename]
    rw [<- renameSubstCommute]
    apply StepEta.eta
    simp [zFree, renFree]
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

--------------

def EtaSubst {Γ} {Δ} (sub1 sub2 : Subst Γ Δ) : Type :=
  {x : Var Γ} → closure StepEta (sub1 x) (sub2 x)

-- theorem parSubstExts {Γ Δ} {sub1 sub2 : Subst Γ Δ}
--   (ps : ParSubst sub1 sub2)
--   : ParSubst (exts sub1) (exts sub2) := by
--   intro x
--   cases x
--   . apply Par.pvar
--   . apply parRename; apply ps

-- theorem substPar {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ}
--   (ps : ParSubst sub1 sub2) (p : Par M M')
--   : Par (subst sub1 M) (subst sub2 M') :=
--   match p with
--   | Par.pvar => ps
--   | Par.papp p1 p2 => Par.papp (substPar ps p1) (substPar ps p2)
--   | Par.pbeta p1 p2 => by
--     rw [<- substCommute]
--     apply Par.pbeta
--     apply substPar
--     apply parSubstExts
--     apply ps
--     apply p1
--     apply substPar
--     apply ps
--     apply p2
--   | Par.plam p => by
--     apply Par.plam
--     apply substPar
--     apply parSubstExts
--     apply ps
--     apply p

-- def parSubstZero {Γ} {M M' : Term Γ}
--   (p : Par M M') : ParSubst (substZero M) (substZero M')
--   := fun {x} =>
--     match x with
--     | Var.zero => p
--     | Var.succ _x' => Par.pvar

theorem subEta {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : closure StepEta N N') (p2 : closure StepEta M M')
  : closure StepEta (subLast N M) (subLast N' M') :=
  sorry
  -- substPar (parSubstZero p2) p1
---------------

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

theorem stepEtaZFree {n1 n2} {M N : Term n2} (step : StepEta M N) {ren : Ren n1 n2}
  (rf : renFree ren M) : renFree ren N :=
  match step with
  | StepEta.app1 p => Iff.mp appRenFree
    ⟨stepEtaZFree p (And.left (Iff.mpr appRenFree rf))
    , (And.right (Iff.mpr appRenFree rf))⟩  
  | StepEta.app2 p => Iff.mp appRenFree
    ⟨(And.left (Iff.mpr appRenFree rf))
    , stepEtaZFree p (And.right (Iff.mpr appRenFree rf))⟩  
  | StepEta.lam p => Iff.mp lamRenFree (stepEtaZFree p (Iff.mpr lamRenFree rf))
  | StepEta.eta zf =>
    let ⟨t, p⟩ := And.left (Iff.mpr appRenFree (Iff.mpr lamRenFree rf))
    ⟨subLast t dummy, (by 
      rw [<- renameSubstCommute]
      rw [p]
      rfl
      ) ⟩

theorem stepZFree {n1 n2} {M N : Term n2} (step : Step M N) {ren : Ren n1 n2}
  (rf : renFree ren M) : renFree ren N := by sorry


-- TODO: I think that this version doesn't hold for single step eta
-- theorem substEta {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ}
--   (ps : EtaSubst sub1 sub2) (p : StepEta M M')
--   : StepEta (subst sub1 M) (subst sub2 M') :=
--   match p with
--   | StepEta.app1 p => by
--     simp [subst]
--     apply StepEta.app1
--     --
--   | StepEta.app2 p => _
--   | StepEta.eta p => _
--   | StepEta.lam p => _

theorem substEta {Γ Δ} {sub : Subst Γ Δ} {M M' : Term Γ}
  (p : StepEta M M')
  : StepEta (subst sub M) (subst sub M') :=
  match p with
  | StepEta.app1 p => StepEta.app1 (substEta p)
  | StepEta.app2 p => StepEta.app2 (substEta p)
  | StepEta.lam p => StepEta.lam (substEta p)
  | @StepEta.eta _ M zf => by
    simp [subst]
    simp [subLast]
    rw [subSub]
    rw [<- substZeroSub]
    rw [<- subSub]
    apply StepEta.eta
    simp [zFree, renFree] at *
    apply Exists.elim; apply zf; intro t' eq
    exists (subst sub t')
    have eq' : subst (exts sub) (rename (Var.succ) t') = subst (exts sub) M := by
      apply congrArg
      apply eq
    rw [<- commuteSubstRename]
    apply eq'
    intro x
    cases x
    . rfl
    . rfl

theorem substStep {Γ Δ} {sub : Subst Γ Δ} {M M' : Term Γ}
  (p : Step M M')
  : closeRef Step (subst sub M) (subst sub M') := by sorry

def rfStepEta {Γ} := closeRef (@StepEta Γ)

theorem etaProperty {Γ} : square (@StepEta Γ) (@StepEta Γ)
  (closeRef (@StepEta Γ)) (closeRef (@StepEta Γ)) :=
  fun p1 p2 =>
  match p1, p2 with
  | StepEta.app1 s1, StepEta.app1 s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨app u _, liftRef (fun x => app x _) StepEta.app1 bla1, liftRef (fun x => app x _) StepEta.app1 bla2⟩
  | StepEta.app1 s1, StepEta.app2 s2 =>
    ⟨_, Sum.inr (StepEta.app2 s2), Sum.inr (StepEta.app1 s1)⟩
  | StepEta.app2 s1, StepEta.app1 s2 => -- REPEATED CASE
    ⟨_, Sum.inr (StepEta.app1 s2), Sum.inr (StepEta.app2 s1)⟩
  | StepEta.app2 s1, StepEta.app2 s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨app _ u, liftRef (app _) StepEta.app2 bla1, liftRef (app _) StepEta.app2 bla2⟩
  | StepEta.lam s1, StepEta.lam s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨lam u, liftRef lam StepEta.lam bla1, liftRef lam StepEta.lam bla2⟩
  | StepEta.eta zf1, StepEta.eta zf2 => ⟨_, Sum.inl (Proof.proof rfl), Sum.inl (Proof.proof rfl)⟩
  | StepEta.lam (StepEta.app1 s), StepEta.eta zf =>
    ⟨_, Sum.inr (StepEta.eta (stepEtaZFree s zf)), Sum.inr (substEta s)⟩
  | StepEta.eta zf, StepEta.lam (StepEta.app1 s) => -- REPEATED CASE
    ⟨_, Sum.inr (substEta s), Sum.inr (StepEta.eta (stepEtaZFree s zf))⟩
-- theorem etaDiamond {Γ} {t t1 t2 : Term Γ}
--   (p1 : StepEta t t1) (p2 : StepEta t t2)
--   : Σ t', StepEta t1 t' × StepEta t2 t' :=

theorem betaEtaCommuteProperty {Γ}
  : square (@Step Γ) (@StepEta Γ) (closure (@StepEta Γ)) (closeRef (@Step Γ)) :=
    fun {t} {tLeft} {tRight} p1 p2 =>
    match p1, p2 with
    | Step.app1 p1, StepEta.app1 p2 =>
      let ⟨t', q1, q2⟩ := betaEtaCommuteProperty p1 p2 
      ⟨_, liftCsr (fun x => app x _) StepEta.app1 q1,
        liftRef (fun x => app x _) Step.app1 q2⟩ 
    | Step.app2 p1, StepEta.app2 p2 =>
      let ⟨t', q1, q2⟩ := betaEtaCommuteProperty p1 p2 
      ⟨_, liftCsr (app _) StepEta.app2 q1,
        liftRef (app _) Step.app2 q2⟩
    | Step.lam p1, StepEta.lam p2 =>
      let ⟨t', q1, q2⟩ := betaEtaCommuteProperty p1 p2 
      ⟨_, liftCsr lam StepEta.lam q1,
        liftRef lam Step.lam q2⟩ 
    | Step.app1 p1, StepEta.app2 p2 =>
      ⟨_, oneStep (StepEta.app2 p2),
        Sum.inr (Step.app1 p1)⟩
    | Step.app2 p1, StepEta.app1 p2 => -- REPEATED CASE
      ⟨_, oneStep (StepEta.app1 p2)
          , Sum.inr (Step.app2 p1)⟩
    | Step.beta, StepEta.app2 p => ⟨_, subEta closure.refl (oneStep p), Sum.inr Step.beta⟩
    | Step.beta, StepEta.app1 (StepEta.lam p) => ⟨_, subEta (oneStep p) closure.refl, Sum.inr Step.beta⟩
    | Step.beta, StepEta.app1 (StepEta.eta zf) => ⟨_, closure.refl, (by
        rw [subLastZFree (d1 := dummy)]
        apply Sum.inl (Proof.proof rfl)
        apply zf
        )⟩
    | Step.lam (Step.app1 p), StepEta.eta zf => ⟨_, oneStep (StepEta.eta (stepZFree p zf)), substStep p⟩
    | Step.lam Step.beta, @StepEta.eta _ (lam a) zf =>
      ⟨_, closure.refl, Sum.inl (Proof.proof (by
        --
        apply Exists.elim; apply (Iff.mpr lamRenFree zf); intro t proof
        -- rw [<- proof]
        simp [subLast, subst]
        rw [<- proof]
        rw [renameSubst]
        rw [renameSubst]
        apply congrArg (fun sub => subst sub _)
        apply funext
        intro x
        exact (match x with
        | Var.zero => rfl
        | Var.succ Var.zero => rfl
        | Var.succ (Var.succ x') => rfl
        )))⟩
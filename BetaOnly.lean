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

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-------- Relations - from Nipkow (2001)
def Relation (A : Type) : Type 1 := A → A → Type

inductive Proof (P : Prop) : Type
| proof : P → Proof P

def closeRef {A} (R : Relation A) : Relation A :=
  fun x y => (Proof (x = y)) ⊕ R x y

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

-- def liftCsr2 {A} {B} {R : Relation A} {R' : Relation B} {R'' : Relation C}
--   {x y : A} {z w : B} (f : A → B → C)
--   (ctr : ∀{x y z w}, R x y → R' z w → R'' (f x z) (f y w))
--   : closure R x y → closure R' z w → closure R'' (f x z) (f y w) :=
--   fun s1 s2 => match s1, s2 with
--   | closure.refl, closure.refl => closure.refl
--   | closure.cons xy yz, s2 => closure.cons (ctr xy) _ -- (liftCsr f ctr yz)


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


-- TODO:
-- Define x ~~ y as ∃ z. R x z ∧ R y z
-- Equivalence R -> Equivalence (closure R) ??? closure is always equivalence
-- Show that if f x ~R g x,  then f x ~R* g x


theorem parSubstDiamond {Γ} {Δ} : diamond (@ParSubst Γ Δ) :=
  fun p1 p2 =>
    ⟨
      fun x =>
        Sigma.fst (parDiamond (@p1 x) (@p2 x))
     , fun {x} =>
        Prod.fst (Sigma.snd (parDiamond (@p1 x) (@p2 x)))
     , fun {x} =>
        Prod.snd (Sigma.snd (parDiamond (@p1 x) (@p2 x)))
     ⟩

--------------------------------------------------------------------------------
------------- Confluence, and other properties ---------------------------------
--------------------------------------------------------------------------------

-- def Pars {Γ} : Term Γ → Term Γ → Prop := fun a b => Nonempty (closure Par a b)
def Pars {Γ} : Relation (Term Γ) := closure Par

def ParsSubst {Γ} {Δ} (sub1 sub2 : Subst Γ Δ) : Type := closure ParSubst sub1 sub2
  -- {x : Var Γ} → Pars (sub1 x) (sub2 x)

theorem substPars {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ}
  (ps : ParsSubst sub1 sub2) (p : Pars M M')
  : Pars (subst sub1 M) (subst sub2 M') :=
  match ps with
  | closure.refl => by induction p with
      | refl => exact closure.refl
      | cons s _ss ih => exact closure.cons (substPar parRefl s) ih
  | closure.cons s ss => closure.cons (substPar s parRefl) (substPars ss p)

theorem diamondToProperty {A} {R : Relation A}
  (d : diamond R)
  : square R R (closure R) (closeRef R) :=
  fun s1 s2 =>
    let ⟨_, s2', s1'⟩ := d s1 s2
    ⟨_, oneStep s2', Sum.inr s1'⟩ 

theorem parsConfluence {Γ} : confluent (@Par Γ):=
  commutationLemma (diamondToProperty parDiamond)

theorem substConfluence {Γ} {Δ} : confluent (@ParSubst Γ Δ):=
  commutationLemma (diamondToProperty parSubstDiamond)

-- https://leanprover.github.io/theorem_proving_in_lean4/axioms_and_computation.html
-- Look at the part about setoids and Quotient


-- Define 
-- Define QTerm with Setoid and Quotient
-- Define QSubst

def equiv {A} (R : Relation A) : A → A → Prop :=
  fun x y =>
    Nonempty (Σ z, 
    (R x z) × (R y z))

def confluentToEquivalence {A} {R : Relation A}
  : confluent R → Equivalence (equiv (closure R)) :=
  fun conf =>
    {refl := fun x => Nonempty.intro ⟨x, closure.refl, closure.refl⟩
    , symm := fun ⟨z, xz, yz⟩ => ⟨z, yz, xz⟩ 
    , trans := fun (Nonempty.intro ⟨_a, xa, ya⟩)
      (Nonempty.intro ⟨_b, yb, zb⟩) =>
      let ⟨c, ac, bc⟩ := conf ya yb
      Nonempty.intro ⟨c, transitivity xa ac, transitivity zb bc⟩ 
    }

def STerm {Γ} : Setoid (Term Γ) := {
    r := equiv Pars
    , iseqv := confluentToEquivalence parsConfluence
    }

def QTerm (Γ : Context) : Type := @Quotient (Term Γ) STerm

def SSubst {Γ} {Δ} : Setoid (Subst Γ Δ) := {
    r := equiv ParsSubst
    , iseqv := confluentToEquivalence substConfluence
    }

def QSubst (Γ Δ : Context) : Type := @Quotient (Subst Γ Δ) SSubst

-- theorem substEquiv {n1 n2} {sub1 sub2 : Subst n1 n2} {t1 t2 : Term n1}
--   (subEq : equiv ParsSubst sub1 sub2)
--   (tEq : equiv Pars t1 t2)
--   : equiv (subst)

theorem equivLam {Γ} {a1 a2 : Term (succ Γ)}
  (e : equiv Pars a1 a2)
  : equiv Pars (lam a1) (lam a2) :=
  let ⟨b, rb1, rb2⟩ := e
  ⟨lam b, liftCsr lam Par.plam rb1, liftCsr lam Par.plam rb2⟩

theorem parsAppCong {Γ} {a1 b1 a2 b2 : Term Γ}
  (pa : Pars a1 a2) (pb : Pars b1 b2)
  : Pars (app a1 b1) (app a2 b2) :=
  transitivity (liftCsr (fun x => app x _) (fun eq => Par.papp eq parRefl) pa)
    (liftCsr (app _) (Par.papp parRefl) pb)

theorem equivApp {Γ} {a1 b1 a2 b2 : Term Γ}
  (eq1 : equiv Pars a1 a2) (eq2 : equiv Pars b1 b2)
  : equiv Pars (app a1 b1) (app a2 b2) :=
  let ⟨a, ra1, ra2⟩ := eq1
  let ⟨b, rb1, rb2⟩ := eq2
  ⟨app a b,
    parsAppCong ra1 rb1
    , parsAppCong ra2 rb2⟩

def qapp {Γ} : QTerm Γ → QTerm Γ → QTerm Γ :=   
  fun a b => Quotient.lift₂ (s₁ := STerm) (s₂ := STerm)
    (fun t1 t2 => Quotient.mk STerm (app t1 t2))
    (fun _ _ _ _ eq1 eq2 =>
      Quotient.sound (equivApp eq1 eq2)) a b

def qlam {Γ} : QTerm (succ Γ) → QTerm Γ :=   
  fun t => Quotient.lift (s := STerm)
    ((Quotient.mk STerm) ∘ lam)
    (fun _ _ eq => (Quotient.sound (equivLam eq))) t

def qvar {Γ} : Var Γ → QTerm Γ := fun x => 
  Quotient.mk STerm (var x)

def qsubst {n1 n2} (sub : QSubst n1 n2) (t : QTerm n1) : QTerm n2 :=
  Quotient.lift₂ (s₁ := SSubst) (s₂ := STerm) (fun sub t => Quotient.mk STerm (subst sub t))
    (fun _sub1 _t1 _sub2 _t2 subEq tEq =>
      let (Nonempty.intro ⟨sub, Rsub1, Rsub2⟩) := subEq 
      let (Nonempty.intro ⟨t, Rt1, Rt2⟩) := tEq 
      -- let (Nonempty.intro blasdf) := subEq 
      Quotient.sound (Nonempty.intro
        ⟨subst sub t, substPars Rsub1 Rt1, substPars Rsub2 Rt2⟩))
      sub t

def qweaken {n} (t : QTerm n) : QTerm (succ n) :=
  qsubst (Quotient.mk SSubst (renToSub Var.succ)) t

theorem parsSubstExts {Γ Δ} {sub1 sub2 : Subst Γ Δ}
  (ps : ParsSubst sub1 sub2)
  : ParsSubst (exts sub1) (exts sub2) :=
  match ps with
  | closure.refl => closure.refl
  | closure.cons s ss => closure.cons (parSubstExts s) (parsSubstExts ss)

def parsSubstZero {Γ} {M M' : Term Γ}
  (ps : Pars M M') : ParsSubst (substZero M) (substZero M') :=
  match ps with
  | closure.refl => closure.refl
  | closure.cons s ss => closure.cons (parSubstZero s) (parsSubstZero ss)

-- def substZero {Γ} (t : Term Γ) : Subst (succ Γ) Γ :=
def qSubstZero {Γ} (t : QTerm Γ) : QSubst (succ Γ) Γ :=
  Quotient.lift (s := STerm)
    (fun t => Quotient.mk SSubst (substZero t))
    (fun _ _ eq =>
      let (Nonempty.intro ⟨t, R1, R2⟩) := eq
      Quotient.sound (Nonempty.intro ⟨substZero t, parsSubstZero R1, parsSubstZero R2⟩))
    t

-- def exts {n1 n2} (sub : Subst n1 n2) : Subst (succ n1) (succ n2) :=
def qexts {n1 n2} (qsub : QSubst n1 n2) : QSubst (succ n1) (succ n2) :=
  Quotient.lift (s := SSubst)
    (fun sub => Quotient.mk SSubst (exts sub))
    (fun _sub1 _sub2 eq =>
      let (Nonempty.intro ⟨sub, R1, R2⟩) := eq
      Quotient.sound (Nonempty.intro ⟨exts sub, parsSubstExts R1, parsSubstExts R2⟩))
    qsub

-- qsubst s (qapp t1 t2) -> qapp (qsubst s t1) (qsubst s t2)
theorem ruleSubstApp {n1 n2} {q1 q2 : QTerm n1}
  {sub : QSubst n1 n2}
  : qsubst sub (qapp q1 q2) = qapp (qsubst sub q1) (qsubst sub q2)
  := by
    revert q1
    apply Quotient.ind
    intro t1
    revert q2
    apply Quotient.ind
    intro t2
    revert sub
    apply Quotient.ind
    intro sub
    simp [qsubst, Quotient.lift₂, Quotient.lift, Quotient.mk, Quot.lift, qapp]
    rfl

-- qsubst s (qlam t) -> qlam (qsubst (exts s) t)
theorem ruleSubstLam {n1 n2} {q : QTerm (succ n1)}
  {sub : QSubst n1 n2}
  : qsubst sub (qlam q) = qlam (qsubst (qexts sub) q)
  := by
    revert q
    apply Quotient.ind
    intro t
    revert sub
    apply Quotient.ind
    intro sub
    simp [qsubst, Quotient.lift₂, Quotient.lift, Quotient.mk, Quot.lift, qapp]
    rfl

-- theorem ruleWeakenLambda {n} {q : QTerm (succ (succ n))}
--   : qweaken (qlam q) = qlam _ := _

-- qsubst s (q (var i)) -> s i
theorem ruleSubstVar {n1 n2} {i : Var n1} -- I'm not sure exacly how else I should implement this
  {sub : Subst n1 n2}
  : qsubst (Quotient.mk SSubst sub) (qvar i) = Quotient.mk STerm (sub i) := rfl

-- qsubst (substZero _) (weaken t) = t
theorem ruleCancelWeakenSubstZero {n} {t : QTerm n}
  {t2 : QTerm n}
  : qsubst (qSubstZero t2) (qweaken t) = t := by
    revert t
    apply Quotient.ind
    intro t
    revert t2
    apply Quotient.ind
    intro t2
    simp [qsubst, qSubstZero, qweaken, Quotient.lift₂, Quotient.lift, Quotient.mk, Quot.lift]
    rw [subSub]
    have lemma : (compose (renToSub Var.succ) (substZero t2)) = ids := by
      apply funext
      intro x
      cases x
      . rfl
      . rfl
    rw [lemma]
    rw [subId]

-- qsubst (substZero t1) 0 -> t1
theorem ruleSubVarZero {n} {t : QTerm n}
  : qsubst (qSubstZero t) (qvar Var.zero) = t := by
    revert t
    apply Quotient.ind
    intro t
    simp [qsubst, Quotient.lift₂, Quotient.lift, Quot.lift, qSubstZero]
    rfl

-- (exts s) (succ i) -> weaken (s i)
theorem ruleSubVarSuc {n1 n2} {i : Var n1}
  {sub : QSubst n1 n2}
  : qsubst (qexts sub) (qvar (Var.succ i)) = qweaken (qsubst sub (qvar i)) := by
    revert sub
    apply Quotient.ind
    intro sub
    simp [qsubst, Quotient.lift₂, Quotient.lift, Quotient.mk, Quot.lift, qexts, qvar, qweaken, subst
      , renToSub, subst]
    apply congrArg
    simp [exts, ids]
    rw [renameSubstRen]
    rfl

-- qapp (qlam t1) t2 -> qsubst (substZero t2) t1
theorem ruleBeta {n} {t1 : QTerm (succ n)} {t2 : QTerm n}
  : qapp (qlam t1) t2 = qsubst (qSubstZero t2) t1 := by
  revert t1
  apply Quotient.ind
  intro t1
  revert t2
  apply Quotient.ind
  intro t2
  simp [qsubst, qSubstZero, qweaken, Quotient.lift₂, Quotient.lift, Quotient.mk, Quot.lift
    , qapp, qlam]
  apply Quotient.sound
  exact ⟨_, oneStep (Par.pbeta parRefl parRefl), closure.refl⟩ 

--------------------------------------------------------------------------------

theorem exampleProof1 {X : QTerm zero}
  : qapp (qlam (qvar Var.zero)) X = X := by
  rw [ruleBeta]
  rw [ruleSubVarZero]

theorem exampleProof2 {X : QTerm zero}
  : qapp (qlam (qlam (qvar (Var.succ Var.zero)))) X = qlam (qweaken X) := by
  rw [ruleBeta]
  rw [ruleSubstLam]
  rw [ruleSubVarSuc]
  rw [ruleSubVarZero]

theorem exampleProof3
  : @qapp zero (qlam (qlam (qvar (Var.succ Var.zero)))) (qlam (qvar Var.zero))
    = qlam (qlam (qvar Var.zero)) := by
  rw [ruleBeta]
  rw [ruleSubstLam]
  rw [ruleSubVarSuc]
  rw [ruleSubVarZero]
  sorry
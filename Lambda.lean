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

| eta : ∀{Γ} {N : Term Γ},
    Step (lam (app (rename Var.succ N) (var Var.zero))) N

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
  | zero => none
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
  {x : Var Γ} →Par (sub1 x) (sub2 x)

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

inductive MultiPar : ∀{Γ}, Term Γ → Term Γ → Type
| halt : {M : Term Γ} → MultiPar M M 
| step : {L M N : Term Γ}
  → Par L M → MultiPar M N → MultiPar L N

-- While on paper the Takahashi method leads to a cleaner proof, in a a theorem prover the proof
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
def Relation (A : Type) : Type := A → A → Prop

def closeRef {A} (R : Relation A) : Relation A :=
  fun x y => x = y \/ R x y

inductive closeTransRef {A} (R : Relation A) : A → A → Prop  
| refl : ∀{a : A}, closeTransRef R a a
| inject : ∀{x y : A}, R x y → closeTransRef R x y 
| trans : ∀{x y z : A}, closeTransRef R x y → closeTransRef R y z → closeTransRef R x z  

def liftRef {A} {B} {R : Relation A} {R' : Relation B} {x y : A} (f : A → B)
  (ctr : R x y → R' (f x) (f y))
  : closeRef R x y → closeRef R' (f x) (f y) :=
  fun s => match s with 
  | Or.inl rfl => Or.inl rfl
  | Or.inr s' => Or.inr (ctr s')

def square {A} (R S T U : Relation A) : Prop :=
  {x y z : A} → R x y → S x z → ∃ u, T y u ∧ U z u     

--     x --R-- y
--     |       |
--     S       T
--     |       |
--     z --U-- u


------- Eta

def dummy : ∀{Γ}, Term Γ := lam (var Var.zero)

def renFree {Γ1 Γ2} (ren : Ren Γ1 Γ2) (t : Term Γ2) : Prop :=
  ∃ t', rename ren t' = t 

def zFree {Γ} (t : Term (succ Γ)) : Prop := renFree Var.succ t

inductive StepEta : ∀{Γ}, Term Γ → Term Γ → Prop where  
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

def EtaSubst {Γ} {Δ} (sub1 sub2 : Subst Γ Δ) : Prop :=
  {x : Var Γ} → StepEta (sub1 x) (sub2 x)

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

def rfStepEta {Γ} := closeRef (@StepEta Γ)

def app1' {Γ} {a1 a2 b : Term Γ} (s : rfStepEta a1 a2)
  : rfStepEta (app a1 b) (app a2 b) :=
  match s with
  | Or.inl rfl => Or.inl rfl
  | Or.inr s' => Or.inr (StepEta.app1 s')


theorem etaProperty {Γ} : square (@StepEta Γ) (@StepEta Γ)
  (closeRef (@StepEta Γ)) (closeRef (@StepEta Γ)) :=
  fun p1 p2 =>
  match p1, p2 with
  | StepEta.app1 s1, StepEta.app1 s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨app u _, liftRef (fun x => app x _) StepEta.app1 bla1, liftRef (fun x => app x _) StepEta.app1 bla2⟩
  | StepEta.app1 s1, StepEta.app2 s2 =>
    ⟨_, Or.inr (StepEta.app2 s2), Or.inr (StepEta.app1 s1)⟩
  | StepEta.app2 s1, StepEta.app1 s2 => -- REPEATED CASE
    ⟨_, Or.inr (StepEta.app1 s2), Or.inr (StepEta.app2 s1)⟩
  | StepEta.app2 s1, StepEta.app2 s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨app _ u, liftRef (app _) StepEta.app2 bla1, liftRef (app _) StepEta.app2 bla2⟩
  | StepEta.lam s1, StepEta.lam s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨lam u, liftRef lam StepEta.lam bla1, liftRef lam StepEta.lam bla2⟩
  | StepEta.eta zf1, StepEta.eta zf2 => ⟨_, Or.inl rfl, Or.inl rfl⟩
  | StepEta.lam (StepEta.app1 s), StepEta.eta zf =>
    ⟨_, Or.inr (StepEta.eta (stepEtaZFree s zf)), Or.inr (substEta s)⟩
  | StepEta.eta zf, StepEta.lam (StepEta.app1 s) => -- REPEATED CASE
    ⟨_, Or.inr (substEta s), Or.inr (StepEta.eta (stepEtaZFree s zf))⟩
-- theorem etaDiamond {Γ} {t t1 t2 : Term Γ}
--   (p1 : StepEta t t1) (p2 : StepEta t t2)
--   : Σ t', StepEta t1 t' × StepEta t2 t' :=

theorem betaEtaCommuteProperty {Γ}
  : square (@Step Γ) (@StepEta Γ) (closeTransRef (@StepEta Γ)) (closeRef (@Step Γ)) :=
    _
    -- fun p1 p2 =>
    -- match p1, p2 with
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

theorem substCommute {n1 n2} {N : Term (succ n1)} {M : Term n1} {sub : Subst n1 n2}
  : subLast (subst (exts sub) N) (subst sub M)
    = subst sub (subLast N M) := by
  simp [subLast]
  -- rw [extsConsShift]
  -- rw [substZConsIds]
  -- rw [substZConsIds]
  rw [subSub, subSub]
  have p : (compose (exts sub) (substZero (subst sub M))) = (compose (substZero M) sub)
    := by
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
  rw [p]

theorem renameSubstCommute {Γ Δ} {N : Term (succ Γ)} {M : Term Γ} {ren : Ren Γ Δ}
  : subLast (rename (ext ren) N) (rename ren M) = rename ren (subLast N M) := by
  rw [renameSubstRen]
  rw [renameSubstRen]
  rw [renameSubstRen]
  rw [renExt]
  rw [substCommute]

--------------------------------------------------------------------------------
-- ANOTHER TRY HERE

def dummy : ∀{Γ}, Term Γ := lam (var Var.zero)

def renFree {Γ1 Γ2} (ren : Ren Γ1 Γ2) (t : Term Γ2) : Prop :=
  ∃ t', rename ren t' = t 

def zFree {Γ} (t : Term (succ Γ)) : Prop := renFree Var.succ t

inductive Par3 : ∀{Γ}, Term Γ → Term Γ → Bool → Type   
| pvar : ∀{Γ} {x : Var Γ}, Par3 (var x) (var x) false
| plam : ∀{Γ} {N N' : Term (succ Γ)},
  Par3 N N' b → Par3 (lam N) (lam N') false
| papp : ∀{Γ b1 b2}{L L' M M' : Term Γ},
  Par3 L L' b1 → Par3 M M' b2 → Par3 (app L M) (app L' M') false
| pbeta : ∀{Γ b1 b2}{N N' : Term (succ Γ)} {M M' : Term Γ},
  Par3 N N' b1 → Par3 M M' b2 → Par3 (app (lam N) M) (subLast N' M') false
| peta : ∀{Γ} {M M' : Term (succ Γ)},
  (p : Par3 M M' false)
  → zFree M
  → Par3 (lam (app M (var Var.zero))) (subLast M' dummy) true -- The idea to use subsitution here is from Nipkow 2001

def Par3' {Γ} (t1 t2 : Term Γ) : Type := Σ b, Par3 t1 t2 b

theorem parRefl3 {Γ} {M : Term Γ} : Σ b, Par3 M M b := by sorry

theorem subPar3 {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : Par3' N N') (p2 : Par3' M M')
  : Par3' (subLast N M) (subLast N' M') := by sorry

-- I don't think the proof would work out anyway- how do we know that the things in etas in the outputs aren't etas anyway?
theorem parDiamond3 {Γ b1 b2} {t t1 t2 : Term Γ}
  (p1 : Par3 t t1 b1) (p2 : Par3 t t2 b2)
  : Σ t', Par3' t1 t' × Par3' t2 t' :=
  match p1, p2 with
  | Par3.pvar, Par3.pvar => ⟨_, ⟨_, Par3.pvar⟩, ⟨_, Par3.pvar⟩⟩
  | Par3.papp a1 b1, Par3.papp a2 b2 =>
    let ⟨a, ⟨_, pa1⟩, ⟨_, pa2⟩⟩ := parDiamond3 a1 a2
    let ⟨b, ⟨_, pb1⟩, ⟨_, pb2⟩⟩ := parDiamond3 b1 b2
    ⟨app a b, ⟨_, Par3.papp pa1 pb1⟩, ⟨_, Par3.papp pa2 pb2⟩⟩ 
  | Par3.pbeta a1 b1, Par3.pbeta a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond3 a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond3 b1 b2
    ⟨subLast a b, subPar3 pa1 pb1, subPar3 pa2 pb2⟩
  | Par3.papp (Par3.plam a1) b1, Par3.pbeta a2 b2 =>
    let ⟨a, ⟨_, pa1⟩, pa2⟩ := parDiamond3 a1 a2
    let ⟨b, ⟨_, pb1⟩, pb2⟩ := parDiamond3 b1 b2
    ⟨subLast a b, ⟨_, Par3.pbeta pa1 pb1⟩ , subPar3 pa2 pb2⟩
  | Par3.pbeta a1 b1, Par3.papp (Par3.plam a2) b2 => -- REPEATED CASE
    let ⟨a, pa1, ⟨_, pa2⟩⟩ := parDiamond3 a1 a2
    let ⟨b, pb1, ⟨_, pb2⟩⟩ := parDiamond3 b1 b2
    ⟨subLast a b, subPar3 pa1 pb1, ⟨_, Par3.pbeta pa2 pb2⟩⟩
  | Par3.papp (Par3.peta zf a1) b1, Par3.pbeta a2 b2 => _
  | Par3.pbeta a1 b1, Par3.papp (Par3.peta zf a2) b2 => _ -- REPEATED CASE
  | Par3.plam a1, Par3.plam a2 =>
    let ⟨a, ⟨_, pa1⟩, ⟨_, pa2⟩⟩ := parDiamond3 a1 a2
    ⟨lam a, ⟨_, Par3.plam pa1⟩, ⟨_, Par3.plam pa2⟩⟩
  | Par3.plam (Par3.papp x y), Par3.peta zf a2 => _
  | Par3.plam (Par3.pbeta x y), Par3.peta (Par3.plam p) zf => _
  | Par3.peta zf t1, Par3.plam t2 => _ -- REPEATED CASE
  | Par3.peta a1 zf1, Par3.peta a2 zf2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond3 a1 a2
    ⟨subLast a dummy, subPar3 pa1 parRefl3, subPar3 pa2 parRefl3⟩

--------------------------------------------------------------------------------
-- ANOTHER TRY HERE

inductive Par2 : ∀{Γ}, Term Γ → Term Γ → Type   
| pvar : ∀{Γ} {x : Var Γ}, Par2 (var x) (var x)
| plam : ∀{Γ} {N N' : Term (succ Γ)},
  Par2 N N' → Par2 (lam N) (lam N')  
| papp : ∀{Γ}{L L' M M' : Term Γ},
  Par2 L L' → Par2 M M' → Par2 (app L M) (app L' M')   
| pbeta : ∀{Γ}{N N' : Term (succ Γ)} {M M' : Term Γ},
  Par2 N N' → Par2 M M' → Par2 (app (lam N) M) (subLast N' M')
| peta : ∀{Γ} {M M' : Term (succ Γ)},
  (p : Par2 M M')
  → zFree M
  → Par2 (lam (app M (var Var.zero))) (subLast M' dummy) -- The idea to use subsitution here is from Nipkow 2001

theorem parRefl2 {Γ} {M : Term Γ} : Par2 M M := by
  induction M with
  | var i => apply Par2.pvar
  | app t1 t2 ih1 ih2 => apply Par2.papp; apply ih1; apply ih2
  | lam t ih => apply Par2.plam; apply ih

theorem subPar2 {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : Par2 N N') (p2 : Par2 M M')
  : Par2 (subLast N M) (subLast N' M') := by sorry

-- inductive NoRepeatedEta : ∀{Γ} {t1 t2 : Term Γ}, Par2 t1 t2 → Type
-- | var : ∀{Γ x}, NoRepeatedEta

theorem parDiamond {Γ} {t t1 t2 : Term Γ}
  (p1 : Par2 t t1) (p2 : Par2 t t2)
  : Σ t', Par2 t1 t' × Par2 t2 t' :=
  match p1, p2 with
  | Par2.pvar, Par2.pvar => ⟨_, Par2.pvar, Par2.pvar⟩
  | Par2.papp a1 b1, Par2.papp a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨app a b, Par2.papp pa1 pb1, Par2.papp pa2 pb2⟩
  | Par2.pbeta a1 b1, Par2.pbeta a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subLast a b, subPar2 pa1 pb1, subPar2 pa2 pb2⟩
  | Par2.papp (Par2.plam a1) b1, Par2.pbeta a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subLast a b, Par2.pbeta pa1 pb1, subPar2 pa2 pb2⟩
  | Par2.pbeta a1 b1, Par2.papp (Par2.plam a2) b2 => -- REPEATED CASE
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subLast a b, subPar2 pa1 pb1, Par2.pbeta pa2 pb2⟩
  | Par2.papp (Par2.peta zf a1) b1, Par2.pbeta a2 b2 => _
  | Par2.pbeta a1 b1, Par2.papp (Par2.peta zf a2) b2 => _ -- REPEATED CASE
  | Par2.plam a1, Par2.plam a2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    ⟨lam a, Par2.plam pa1, Par2.plam pa2⟩
  | Par2.plam a1, Par2.peta zf a2 => _
  | Par2.peta zf t1, Par2.plam t2 => _ -- REPEATED CASE
  | Par2.peta a1 zf1, Par2.peta a2 zf2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    ⟨subLast a dummy, subPar2 pa1 parRefl2, subPar2 pa2 parRefl2⟩

--------------------------------------------------------------------------------
---------- This section came from Confluence.agda in plfa ----------------------
--------------------------------------------------------------------------------
-- I have modified this section from PLFA to handle eta

inductive Par : ∀{Γ}, Term Γ → Term Γ → Type   
| pvar : ∀{Γ} {x : Var Γ}, Par (var x) (var x)
| plam : ∀{Γ} {N N' : Term (succ Γ)},
  Par N N' → Par (lam N) (lam N')  
| papp : ∀{Γ}{L L' M M' : Term Γ},
  Par L L' → Par M M' → Par (app L M) (app L' M')   
| pbeta : ∀{Γ}{N N' : Term (succ Γ)} {M M' : Term Γ},
  Par N N' → Par M M' → Par (app (lam N) M) (subLast N' M')  
| peta : ∀{Γ} {M M' : Term Γ},
  Par M M'
  → Par (lam (app (rename Var.succ M) (var Var.zero))) M'
-- | peta : ∀{Γ} {M M' : Term (succ Γ)},
--   Par M M'
-- → zFree M
--   → Par (lam (app M (var Var.zero))) (subLast M' dummy)

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
  | peta _p ih =>
    intros
    simp [rename]
    rw [composeRename]
    have lemma {n1 n2} {ren : Ren n1 n2}: ext ren ∘ Var.succ = Var.succ ∘ ren := by
      apply funext
      intro x
      rfl
    rw [lemma]
    rw [<- composeRename]
    simp [ext]
    apply Par.peta
    apply ih

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
  | Par.peta p => by
    simp [subst]
    rw [commuteSubstRename]
    apply Par.peta
    apply substPar
    apply ps
    apply p
    intro x
    rfl

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

-- Σ' is called "psigma"
-- would need to generalize so that induction works in lambda case
-- def unweaken {Γ} (t : Term (succ Γ))
--   : Option (Σ' t', rename Var.succ t' = t) :=
--   -- should actually be (does not exists t' such that ...) ⊕ (Σ' t', rename Var.succ t' = t)
--   match t with
--   | var i => match i with
--     | Var.zero => none
--     | Var.succ i' => some ⟨var i', rfl⟩
--   | app t1 t2 => do
--     let ⟨t1', p1⟩ <- unweaken t1
--     let ⟨t2', p2⟩  <- unweaken t2
--     some ⟨app t1' t2', by simp [rename]; apply And.intro; apply p1; apply p2⟩ 
--   | lam t => do
--     let ⟨t', p⟩ <- unweaken t
    -- some ⟨lam t', by simp [rename]; apply p⟩ 

inductive PropToType (P : Prop) : Type
| propToType : P → PropToType P


inductive Decided (P : Prop) : Prop
| yes : P → Decided P 
| no : Not P → Decided P 

inductive DecidedT (T : Type) : Type
| yes : T → DecidedT T 
| no : (T → False) → DecidedT T 

-- TODO: is it called a redEx?
inductive BetaRedex {Γ} : Term Γ → Prop
| redex : ∀ {t1 t2}, BetaRedex (app (lam t1) t2)

inductive EtaRedex : ∀{Γ}, Term Γ → Prop
| redex : ∀ {t}, EtaRedex (lam (app (rename Var.succ t) (var Var.zero)))

inductive TermKind : ∀{Γ}, Term Γ → Type
| betaRedex : ∀{Γ}, (t1 : Term (succ Γ)) → (t2 : Term Γ)
  →  TermKind (app (lam t1) t2)
| app : ∀{Γ}, (t1 t2 : Term Γ) → Not (BetaRedex (app t1 t2)) 
  → TermKind (app t1 t2) 
| etaRedex : ∀{Γ}, (t : Term (succ Γ))
  → zFree t 
  → TermKind (lam (app t (var Var.zero))) 
| lam : ∀{Γ}, (t : Term (succ Γ))
  → Not (EtaRedex (lam t))
  → TermKind (lam t)
| var : ∀{Γ}, (i : Var Γ) → TermKind (var i)

-- Note: this can be proven constructively, but for now I just have used LEM
def unrename {n1 n2} (ren : Ren n1 n2) (t : Term n2)
  : Decided (∃ t', rename ren t' = t) :=
    match (Classical.em (∃ t', rename ren t' = t)) with
    | Or.inl yes => Decided.yes yes
    | Or.inr no => Decided.no no

def unrename2 {n1 n2} (ren : Ren n1 n2) (t : Term n2)
  : DecidedT (Σ' t', rename ren t' = t) := by sorry

def findTermKind {Γ : Context} (t : Term Γ) : TermKind t :=
  match t with
  | (app (lam t1) t2) => TermKind.betaRedex _ _
  | (app (var _) t2) => TermKind.app _ _ (by intro r; cases r)
  | (app (app _ _) t2) => TermKind.app _ _ (by intro r; cases r)
  | (Term.lam t) =>
    let whatIsWrongWithLean {n} (t : Term (succ n)) : TermKind (lam t) :=
      match t with
      | var _ => TermKind.lam _ (by intro r; cases r)
      | lam _ => TermKind.lam _ (by intro r; cases r)
      | app t1 (var (Var.succ _)) => TermKind.lam _ (by intro r; cases r)
      | app t1 (app _ _) => TermKind.lam _ (by intro r; cases r)
      | app t1 (lam _) => TermKind.lam _ (by intro r; cases r)
      | app t1 (var Var.zero) => match unrename2 Var.succ t1 with
        | DecidedT.yes ⟨t', p⟩ => by
          rw [<- p]
          exact TermKind.etaRedex _ ⟨_, rfl⟩ 
        | DecidedT.no p => TermKind.lam _ (by
          intro x
          cases x with
          | @redex t =>
            apply p
            exists t
        )
    whatIsWrongWithLean t
  | (var _) => TermKind.var _


-- See this for lean's features for proving termination:
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html

-- see also: https://www.cs.vu.nl/~jbe248/lv2017/12x4.pdf
-- see https://doi.org/10.1006/inco.1995.1057
-- universal common reduct

-- the Takahashi function
def ucr {Γ} (t : Term Γ) : Term Γ :=
  match findTermKind t with
  | TermKind.betaRedex t1 t2 => subLast (ucr t1) (ucr t2)
  | TermKind.app t1 t2 _p => app (ucr t1) (ucr t2)
  | TermKind.lam t _p => lam (ucr t)
  | TermKind.etaRedex t _p => subLast (ucr t) dummy
  | TermKind.var i => var i

theorem ucrRenCommute {n1 n2} {ren : Ren n1 n2} {t : Term n1}
  -- ucr (rename ren t) = rename ren (ucr t) :=
  : rename ren (ucr t) = ucr (rename ren t) := by
  generalize bla: (findTermKind t) = val
  -- apply Eq.trans
  unfold ucr
  exact (
    match findTermKind t with
    | TermKind.betaRedex t1 t2 => _
    | TermKind.app t1 t2 _p => by
      --
      simp
      --
      apply Eq.trans
      unfold ucr
      have please: findTermKind (app t1 t2) = val := bla
      rw [please]
      simp
      --
      simp [ucr]
      --
    | TermKind.lam t _p => _
    | TermKind.etaRedex t _p => _
    | TermKind.var i => rfl
  )


theorem findKindLam {Γ} {t : Term (succ Γ)} (notRedex : ¬ EtaRedex (lam t))
  : findTermKind (lam t) = TermKind.lam t notRedex :=
  match t, findTermKind (lam t) with
  | .(_), TermKind.lam _ p => rfl
  | .(_), TermKind.etaRedex _ p => by
    apply False.elim
    apply notRedex
    apply Exists.elim
    apply p
    intro t' proof
    rw [<- proof]
    apply EtaRedex.redex

theorem ucrLam {Γ} {t : Term (succ Γ)} (notRedex : ¬ EtaRedex (lam t))
  : ucr (lam t) = lam (ucr t) := by
  apply Eq.trans
  unfold ucr
  rw [findKindLam notRedex]
  simp

theorem ucrEtaRedex {Γ} {t : Term Γ}
  : ucr (lam (app (rename Var.succ t) (var Var.zero))) = ucr t := by
  have lemma : ∃ p, findTermKind (lam (app (rename Var.succ t) (var Var.zero)))
    = TermKind.etaRedex (rename Var.succ t) p :=
    match t, findTermKind (lam (app (rename Var.succ t) (var Var.zero))) with
    | .(_), TermKind.lam _ p => by apply False.elim; apply p; apply EtaRedex.redex
    | .(_), TermKind.etaRedex _ p => by exists p
  --
  apply Eq.trans
  unfold ucr
  apply Exists.elim; apply lemma; intro a proof
  rw [proof]
  simp
  sorry

theorem parTriangle {Γ} {M N : Term Γ} (step: Par M N) : Par N (ucr M) :=
  match findTermKind M with
  | TermKind.betaRedex t1 t2 =>
    match step with
    | Par.pbeta p1 p2 => by
      simp [ucr]
      apply subPar
      apply parTriangle; apply p1
      apply parTriangle; apply p2
    | Par.papp (Par.plam p1) p2 => by
      simp [ucr]
      apply Par.pbeta
      apply parTriangle; apply p1
      apply parTriangle; apply p2
    | Par.papp (Par.peta p1) p2 => by
      simp [ucr]
      sorry
      --
  | TermKind.app t1 t2 notRedex =>
    match step with
    | Par.pbeta p1 p2 => by apply False.elim; apply notRedex; apply BetaRedex.redex
    | Par.papp p1 p2 => _
  | TermKind.lam t notRedex =>
    match step with
    | Par.peta p => by apply False.elim; apply notRedex; apply EtaRedex.redex
    | Par.plam p => by
      simp [ucr]
      rw [ucrLam notRedex]
      apply Par.plam
      apply parTriangle
      apply p
  | TermKind.etaRedex t p =>
    match step with
    | Par.plam p => _
    | Par.peta p => by
      rw [ucrEtaRedex]
      apply parTriangle; apply p
  | TermKind.var i =>
    match step with
    | Par.pvar => parRefl




-- Idea: I will use a direct takahashi proof for beta and eta at once.
-- I will alter the definition of takahashi first using the idea from Nipkow 2001 that
-- I can define eta contraction with substitution on the right instead of renaming
-- on the left. Next, I will also modify the Takahashi function so that
-- takahashi (lam x . t x) where x ∉ t = (takahashi t) [x / dummy] 
--   instead of takahashi (t [x / dummy])
-- This way, it will be recursive on the structure of the terms.
-- I will then later have to prove that 
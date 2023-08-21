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
    Step N (lam (app (rename Var.succ N) (var Var.zero)))

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
  | Nat.succ x' => ext ren

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
---------- This section came from Confluence.agda in plfa ----------------------
--------------------------------------------------------------------------------
-- I have heavily modified this section from PLFA

def SubStep {n1 n2 : Context} (sub1 sub2 : Subst n1 n2) : Type :=
  ∀ {x}, Step (sub1 x) (sub2 x)

def MultiSubStep {n1 n2} (sub1 sub2 : Subst n1 n2) : Type :=
  ∀ {x}, MultiStep (sub1 x) (sub2 x)

def singletonStep {n} {t1 t2 : Term n} (step : Step t1 t2)
  : MultiStep t1 t2 := MultiStep.step step MultiStep.halt

theorem multiSubStepHalt {n1 n2} {sub : Subst n1 n2} : MultiSubStep sub sub := by
  intro x
  apply MultiStep.halt

theorem multiSubStepStep {n1 n2} {sub1 sub2 sub3 : Subst n1 n2}
  (step : SubStep sub1 sub2) (mstep : MultiSubStep sub2 sub3)
  : MultiSubStep sub1 sub3 := by
  intro x
  apply MultiStep.step step mstep

theorem renameStep {n1}
  {t1 t2 : Term n1} (step : Step t1 t2)
  : ∀ {n2} {ren : Ren n1 n2},
    Step (rename ren t1) (rename ren t2) := by 
  induction step with
  -- . simp [rename]; apply Step.app1;  
  | app1 _ ih => intros; simp [rename]; apply Step.app1; apply ih
  | app2 _ ih => intros; simp [rename]; apply Step.app2; apply ih
  | lam _ ih => intros; simp [rename]; apply Step.lam; apply ih
  | beta =>
    intros
    simp [rename]
    rw [<- renameSubstCommute]
    apply Step.beta
  | eta =>
    intros
    simp [rename]
    rw [composeRename]
    -- TODO: decide if this lemma should be defined outside. Is it needed elsewhere?
    have renExtLemma : ∀{n1 n2} {ren : Ren n1 n2}, ext ren ∘ Var.succ = Var.succ ∘ ren := by
      intros
      apply funext
      intro x
      simp [Function.comp]
      simp [ext]
    rw [renExtLemma]
    rw [<- composeRename]
    apply Step.eta

theorem renameMultiStep {n1}
  {t1 t2 : Term n1} {mstep : MultiStep t1 t2}
  : ∀ {n2} {ren : Ren n1 n2},
    MultiStep (rename ren t1) (rename ren t2) := by 
  induction mstep with
  | halt => intros; apply MultiStep.halt
  | step s _ms ih =>
    intros
    apply MultiStep.step
    apply (renameStep s)
    apply ih
  

theorem subStepExts {n1 n2} {sub1 sub2 : Subst n1 n2}
  : SubStep sub1 sub2 → MultiSubStep (exts sub1) (exts sub2) := by 
  intro step x
  cases x with
  | zero => simp [exts]; apply MultiStep.halt
  | succ y => simp [exts]; apply renameMultiStep; apply singletonStep; apply step

theorem subMultiStepExts {n1 n2} {sub1 sub2 : Subst n1 n2}
  : MultiSubStep sub1 sub2 → MultiSubStep (exts sub1) (exts sub2) := by 
  intro mstep x
  cases x with
  | zero => simp [exts]; apply multiSubStepHalt
  | succ y =>
    simp [exts]
    apply renameMultiStep
    apply mstep


theorem substStep {n1}
  {t1 t2 : Term n1} (step : Step t1 t2)
  : ∀ {n2} {sub : Subst n1 n2},
    Step (subst sub t1) (subst sub t2) := by 
  induction step with
  | app1 _ ih => intros; simp [subst]; apply Step.app1; apply ih
  | app2 _ ih => intros; simp [subst]; apply Step.app2; apply ih
  | lam _ ih => intros; simp [subst]; apply Step.lam; apply ih
  | beta =>
    intros
    simp [subst]
    rw [<- substCommute]
    apply Step.beta
  | @eta _ N =>
    intros n2 sub
    simp [subst]
    have lemma : subst (exts sub) (rename Var.succ N) = rename Var.succ (subst sub N) := by
      rw [renameSubstRen]
      rw [renameSubstRen]
      rw [subSub]
      rw [subSub]
      rw [renSuccShift]
      rw [renSuccShift]
      rw [extsConsShift]
      rw [subTail]
    rw [lemma]
    apply Step.eta

theorem substMultiStep {n1}
  {t1 t2 : Term n1} (step : MultiStep t1 t2)
  {n2} {sub : Subst n1 n2}
  : MultiStep (subst sub t1) (subst sub t2) := by 
  induction step with
  | halt => apply MultiStep.halt
  | step s ms ih =>
    apply MultiStep.step
    apply (substStep s)
    apply ih
  
  
theorem stepSubs {n1} {t : Term n1} :
   ∀ {n2} {sub1 sub2 : Subst n1 n2} {_sstep : MultiSubStep sub1 sub2},
    MultiStep (subst sub1 t) (subst sub2 t) := by
  induction t with
  | var x => intro n2 sub1 sub2 sstep; apply sstep
  | app t1 t2 ih1 ih2 =>
    intro n2 sub1 sub2 sstep
    simp [subst]
    apply appCong
    apply ih1; apply sstep
    apply ih2; apply sstep
  | lam t ih =>
    intro n2 sub1 sub2 sstep
    simp [subst]
    apply lamCong
    apply ih
    apply subMultiStepExts
    apply sstep
  
theorem parSubstZero {Γ} {M M' : Term Γ}
   {mstep: MultiStep M M' }
   : MultiSubStep (substZero M) (substZero M') := by
   intro x
   cases x
   . apply mstep
   . simp [substZero]
     apply MultiStep.halt

theorem stepSub {Γ} {N N' : Term (succ Γ)} {M M' : Term Γ}
  (stepN : MultiStep N N') (stepM : MultiStep M M')
  : MultiStep (subLast N M) (subLast N' M') := by
  simp [subLast]
  let lemma : MultiStep (subst (substZero M) N) (subst (substZero M) N') := by
      apply substMultiStep
      apply stepN
  apply (multiTrans lemma)
  apply stepSubs
  apply parSubstZero
  apply stepM

def superStep {Γ} (t : Term Γ) : Term Γ :=
  match t with
  | var x => var x
  | app (lam t1) t2 => subLast (superStep t1) (superStep t2)
  | app t1 t2 => app (superStep t1) (superStep t2)
  | lam t => lam (superStep t)

inductive BetaStep : ∀{Γ}, Term Γ → Term Γ → Type where  
| app1 : ∀ {Γ} {L L' M : Term Γ},
    BetaStep L L'
    → BetaStep (app L M) (app L' M)
| app2 : ∀ {Γ} {L M M' : Term Γ},
    BetaStep M M'
    → BetaStep (app L M) (app L M')
| beta : ∀ {Γ} {N : Term (succ Γ)} {M : Term Γ},
    BetaStep (app (lam N) M) (subLast N M)
| lam : ∀ {Γ} {N N' : Term (succ Γ)},
    BetaStep N N' → BetaStep (lam N) (lam N')

inductive EtaStep : ∀{Γ}, Term Γ → Term Γ → Type where  
| eta : ∀{Γ} {N : Term Γ},
    EtaStep N (lam (app (rename Var.succ N) (var Var.zero)))

theorem selfSuperStep {Γ} {t : Term Γ}
  : MultiStep t (superStep t) :=
  match t with
  | var i => by simp [superStep]; apply MultiStep.halt
  | app (lam t1) t2 => by
    simp [superStep]
    apply MultiStep.step
    apply Step.beta
    apply stepSub
    apply selfSuperStep
    apply selfSuperStep
  | app (app t1 t2) t3 => by
    simp [superStep]
    apply appCong
    apply selfSuperStep
    apply selfSuperStep
  | app (var i) t2 => by
    simp [superStep]
    apply appCong
    apply MultiStep.halt
    apply selfSuperStep
    --
  | lam t => by
    simp [superStep]
    apply lamCong
    apply selfSuperStep

theorem triangleProperty {Γ} {t t' : Term Γ}
  {step : BetaStep t t'}
  : MultiStep t' (superStep t) :=
  match t, t', step with
  | .(_), .(_), BetaStep.lam s => by
    simp [superStep]
    apply lamCong
    apply triangleProperty
    apply s
  | (app (var i) t2), .(_), BetaStep.app2 s => by
    simp [superStep]
    apply appRCong
    apply triangleProperty
    apply s
  | (app (lam t1) t2), .(_), BetaStep.app2 s => by
    simp [superStep]
    apply MultiStep.step
    apply Step.beta
    apply stepSub
    apply selfSuperStep
    apply triangleProperty; apply s
  | (app (app t1 t2) t3), .(_), BetaStep.app2 s => by
    simp [superStep]
    apply appCong
    apply selfSuperStep
    apply triangleProperty; apply s
  | .(_), .(_), BetaStep.beta => by
    simp [superStep]
    apply stepSub
    apply selfSuperStep
    apply selfSuperStep
  | (app (lam t1) t2), .(_), BetaStep.app1 (BetaStep.lam s) => by
    simp [superStep]
    apply MultiStep.step
    apply Step.beta
    apply stepSub
    apply triangleProperty; apply s
    apply selfSuperStep
  | (app (app t1 t2) t3), .(_), BetaStep.app1 s => by
    simp [superStep]
    apply appCong
    apply triangleProperty; apply s
    apply selfSuperStep

theorem betaToStep {n} {t1 t2 : Term n}
  {bstep : BetaStep t1 t2} : Step t1 t2 := by
  induction bstep with
  | app1 _ ih => apply Step.app1; apply ih
  | app2 _ ih => apply Step.app2; apply ih
  | lam _ ih => apply Step.lam; apply ih
  | beta => apply Step.beta

-- theorem stepToBeta {n} {t1 t2 : Term n}
--   {step : Step t1 t2}
--   : BetaStep t1 t2 ⊕ EtaStep t1 t2 := by
--   induction step with
--   | app1 _ ih => apply Sum.inl; apply BetaStep.app1; apply ih
--   | app2 _ ih => apply Sum.inl; apply BetaStep.app2; apply ih
--   | lam _ ih => apply Sum.inl; apply BetaStep.lam; apply ih
--   | beta => apply Sum.inl; apply BetaStep.beta
--   | eta => apply Sum.inr; apply EtaStep.eta

theorem subWeaken {n} {M N : Term n}
  : subLast (rename Var.succ M) N = M := by
  simp [subLast]
  rw [renameSubstRen]
  rw [subSub]
  have lemma: compose (renToSub Var.succ) (substZero N) = ids := by
    apply funext
    intro x
    cases x
    . rfl
    . rfl
  rw [lemma]
  apply subId

theorem betaEtaCaseLemma {Γ} {M : Term Γ} {N : Term (succ Γ)}
  : MultiStep (app (lam (app (rename Var.succ (lam N)) (var Var.zero))) M) (subLast N M)
  := by
     apply MultiStep.step
     apply Step.beta
     have lemma {n} {a : Term (succ n)} {M : Term n}
       : subLast (app (rename Var.succ (lam a)) (var Var.zero)) M
       = app (lam a) M := by
       have lemma2 {n} {a : Term (succ n)} {M : Term n} 
         : subLast (app (rename Var.succ (lam a)) (var Var.zero)) M
           = app (subLast (rename Var.succ (lam a)) M) M := by
           simp [subLast, subst, substZero]
       rw [lemma2]
       rw [subWeaken]
     rw [lemma]
     apply MultiStep.step
     apply Step.beta
     apply MultiStep.halt

theorem singleStepConfluence {Γ} {t t1 t2 : Term Γ}
  (step1 : Step t t1) (step2 : Step t t2)
  : Σ t', MultiStep t1 t' × MultiStep t2 t' :=
  match step1, step2 with
  | Step.lam a, Step.lam b => match singleStepConfluence a b with
    | ⟨t, m1, m2⟩ => ⟨lam t, lamCong m1, lamCong m2⟩
  | Step.app1 a, Step.app1 b => match singleStepConfluence a b with
    | ⟨_, m1, m2⟩ => ⟨_, appLCong m1, appLCong m2⟩
  | Step.app2 a, Step.app2 b => match singleStepConfluence a b with
    | ⟨_, m1, m2⟩ => ⟨_, appRCong m1, appRCong m2⟩
  | Step.app2 a, Step.app1 b => 
    ⟨_, singletonStep (Step.app1 b), singletonStep (Step.app2 a)⟩
  | Step.app1 a, Step.app2 b =>
    ⟨_, singletonStep (Step.app2 b), singletonStep (Step.app1 a)⟩
  | Step.eta, x => ⟨_,
        singletonStep (Step.lam (Step.app1 (renameStep x)))
        , singletonStep Step.eta⟩
  | x, Step.eta => ⟨_,
        singletonStep Step.eta
        , singletonStep (Step.lam (Step.app1 (renameStep x)))⟩ 
  | Step.beta, Step.beta => ⟨_, MultiStep.halt, MultiStep.halt⟩
  | Step.beta, Step.app1 (Step.lam s) => ⟨_, stepSub (singletonStep s) MultiStep.halt,
    singletonStep Step.beta⟩
  | Step.beta, Step.app1 (Step.eta) => ⟨_, MultiStep.halt, betaEtaCaseLemma⟩
  | Step.beta, Step.app2 a =>
    ⟨_, stepSub MultiStep.halt (singletonStep a), singletonStep Step.beta⟩ 
  | Step.app2 a, Step.beta =>
    ⟨_, singletonStep Step.beta, stepSub MultiStep.halt (singletonStep a)⟩ 
  | Step.app1 (Step.lam s), Step.beta => ⟨_, singletonStep Step.beta,
    stepSub (singletonStep s) MultiStep.halt⟩
  | Step.app1 Step.eta, Step.beta => ⟨_, betaEtaCaseLemma, MultiStep.halt⟩

theorem strip {Γ} {t t1 t2 : Term Γ}
  (step1 : Step t t1) (mstep2 : MultiStep t t2)
  : Σ t', MultiStep t1 t' × MultiStep t2 t' :=
  match mstep2 with
  | MultiStep.halt => ⟨_, MultiStep.halt, singletonStep step1⟩
  | MultiStep.step s ms =>
    let bla := singleStepConfluence step1 s
    match strip step1 mstep2 with
    | ⟨t', ms1, ms2⟩ => ⟨_, _⟩

-- theorem confluence {Γ} {t t1 t2 : Term Γ}
--   (mstep1 : MultiStep t t1) (mstep2 : MultiStep t t2)
--   : Σ t', MultiStep t1 t' × MultiStep t2 t' := by
--   induction mstep1 with
--   | halt => exact ⟨_, mstep2, MultiStep.halt⟩
--   | step s1 ms1 ih1 => induction mstep2 with
--             | halt => exact ⟨_, MultiStep.halt, MultiStep.step s1 ms1⟩
--             | step s2 ms2 ih2 => sorry


-- TODO: follow this proof https://doi.org/10.1006/inco.1995.1057

/- 
Something that we will need
Equivalence relation on terms R

lamR : R t1 t2 → R (lam t1) (lam t2)
appR : R a1 a2 → R b1 b2 → R (app a1 b1) (app a2 b2)

prove using *cong
---/


-- Something that is slightly concerning is if the use of funext and/or quotients
-- will make things non-computational in a way what will cause problems.
-- I need to think this through carefully.

-- I believe that the following demonstrates that quotients don't actually
-- get in the way of computation in lean:

def Bla := @Quot Nat (fun x y => x = y)

def getNat : Bla → Nat :=
  Quot.lift (fun x => x) (by
    intros a b p
    simp
    assumption
  )

theorem canICompute : (getNat (Quot.mk (fun x y => x = y) 5)) = 5 := by
  simp

-- Some other very strange reduction behaviour that I noticed: any type with
-- only one constructor won't block reduction, but if you uncomment
-- the second constructor, then it does block reduction.

inductive MyUnit : Type 
| myunit : MyUnit
-- | myunit2 : MyUnit

def test3 : MyUnit → Nat → Nat := fun p n =>
  match p with
  | MyUnit.myunit => n * n + 2
  -- | MyUnit.myunit2 => n * n + 2

axiom typeAxiom : MyUnit

theorem canICompute2 : test3 typeAxiom 2 = 6 := by
  simp [test3]
  --
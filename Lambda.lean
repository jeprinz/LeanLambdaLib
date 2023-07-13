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

theorem subPar {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : Par N N') (p2 : Par M M')
  : Par (subLast N M) (subLast N' M') := by
  sorry

theorem parRefl {Γ} {M : Term Γ} : Par M M := by
  induction M with
  | var i => apply Par.pvar
  | app t1 t2 ih1 ih2 => apply Par.papp; apply ih1; apply ih2
  | lam t ih => apply Par.plam; apply ih

inductive MultiPar {Γ} : Term Γ → Term Γ → Type  
| halt : {M : Term Γ} → MultiPar M M 
| step : {L M N : Term Γ}
  → Par L M → MultiPar M N → MultiPar L N   

-- Σ' is called "psigma"
-- would need to generalize so that induction works in lambda case
def unweaken {Γ} (t : Term (succ Γ))
  : Option (Σ' t', rename Var.succ t' = t) :=
  -- should actually be (does not exists t' such that ...) ⊕ (Σ' t', rename Var.succ t' = t)
  match t with
  | var i => match i with
    | Var.zero => none
    | Var.succ i' => some ⟨var i', rfl⟩
  | app t1 t2 => do
    let ⟨t1', p1⟩ <- unweaken t1
    let ⟨t2', p2⟩  <- unweaken t2
    some ⟨app t1' t2', by simp [rename]; apply And.intro; apply p1; apply p2⟩ 
  | lam t => do
    let ⟨t', p⟩ <- unweaken t
    some ⟨lam t', by simp [rename]; apply p⟩ 

inductive PropToType (P : Prop) : Type
| propToType : P → PropToType P

-- see also: https://www.cs.vu.nl/~jbe248/lv2017/12x4.pdf
-- see https://doi.org/10.1006/inco.1995.1057
-- universal common reduct
-- def ucr {Γ} (t : Term Γ) : Term Γ :=
--   match t with
--   | var x => var x
--   | app (lam t1) t2 => subLast (ucr t1) (ucr t2)
--   | lam term@(app t (var Var.zero)) =>
--     match unrename Var.succ t with
--     | Sum.inl _ => lam (ucr term)
--     | Sum.inr ⟨t', _p⟩ => t'
--   | lam (var i) => lam (ucr (var i))
--   -- | lam (lam t) => lam (ucr (lam t))
--   | lam t => lam (ucr t)
--   | app t1 t2 => app (ucr t1) (ucr t2)

inductive Decided (P : Prop) : Type
| yes : P → Decided P 
| no : Not P → Decided P 

inductive DecidedT (T : Type) : Type
| yes : T → DecidedT T 
| no : (T → False) → DecidedT T 

-- TODO: is it called a redEx?
inductive BetaRedux {Γ} : Term Γ → Prop
| redux : ∀ {t1 t2}, BetaRedux (app (lam t1) t2)

inductive EtaRedux : ∀{Γ}, Term Γ → Prop
| redux : ∀ {t}, EtaRedux (lam (app (rename Var.succ t) (var Var.zero)))

inductive TermKind : ∀{Γ}, Term Γ → Type
| betaRedux : ∀{Γ}, (t1 : Term (succ Γ)) → (t2 : Term Γ)
  →  TermKind (app (lam t1) t2)
| app : ∀{Γ}, (t1 t2 : Term Γ) → Not (BetaRedux (app t1 t2)) 
  → TermKind (app t1 t2) 
| etaRedux : ∀{Γ}, (t : Term Γ)
  → TermKind (lam (app (rename Var.succ t) (var Var.zero))) 
| lam : ∀{Γ}, (t : Term (succ Γ)) → Not (EtaRedux (lam t))
  → TermKind (lam t)
| var : ∀{Γ}, (i : Var Γ) → TermKind (var i)

def test {n} (t : Term (succ n)) : Term (succ n) :=
  match t with
  | var _ => _
  | lam _ => _
  | app _ _ => _

def unrename {n1 n2} (ren : Ren n1 n2) (t : Term n2)
  : DecidedT (Σ' t', rename ren t' = t) :=
  by sorry

theorem findTermKind {Γ : Context} (t : Term Γ) : TermKind t :=
  match t with
  | (app (lam t1) t2) => TermKind.betaRedux _ _
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
      | app t1 (var Var.zero) => match unrename Var.succ t1 with
        | DecidedT.yes ⟨t', p⟩ => by
          rw [<- p]
          exact TermKind.etaRedux _
        | DecidedT.no p => TermKind.lam _ (by
          intro x
          cases x with
          | @redux t =>
            apply p
            exists t
        )
    whatIsWrongWithLean t
  | (var _) => TermKind.var _

theorem decideBetaRedux {Γ} (t : Term Γ) : Decided (BetaRedux t) :=
  match t with
  | (app (lam t1) t2) => Decided.yes BetaRedux.redux
  | (app (var _) t2) => Decided.no (by intro r; cases r)
  | (app (app _ _) t2) => Decided.no (by intro r; cases r)
  | (lam _) => Decided.no (by intro r; cases r)
  | (var _) => Decided.no (by intro r; cases r)

inductive Ucr : ∀{Γ}, Term Γ → Term Γ → Type
| var : ∀{i}, Ucr (var i) (var i)
| beta : ∀{Γ}, {M M': Term (succ Γ)} → {N N' : Term Γ}  → Ucr M M' → Ucr N N' 
  → Ucr (app (lam M) N) (subLast M' N') 
| eta : ∀{Γ}, {M : Term Γ}
  → Ucr (lam (app (rename Var.succ M) (var Var.zero))) M 
| app : ∀{Γ}, {M N M' N' : Term Γ} → Not (BetaRedux (app M N)) 
  → Ucr M M' → Ucr N N' → Ucr (app M N) (app M' N')  
| lam : ∀{Γ}, {M M' : Term (succ Γ)} → Not (EtaRedux (lam M)) 
  → Ucr M M' → Ucr (lam M) (lam M')

theorem ucrExists {Γ} (t : Term Γ) : Σ' t', Ucr t t' :=
  match findTermKind t with
  | TermKind.betaRedux t1 t2 => _
  | TermKind.app t1 t2 p =>
    match ucrExists t1, ucrExists t2 with
    | ⟨t1', p1⟩, ⟨t2', p2⟩ => ⟨app t1' t2', Ucr.app p p1 p2⟩
  | TermKind.lam t p => _
  | TermKind.etaRedux t => _
  | TermKind.var i => _

theorem parTriangle {Γ} {M N : Term Γ} (step: Par M N) : Par N (ucr M) :=
  match M, step with
  | .(_), Par.pvar => by simp [ucr]; apply parRefl
  | .(_), Par.pbeta p1 p2 => by
    simp [ucr]
    apply subPar
    apply parTriangle; apply p1
    apply parTriangle; apply p2
  | .(_), Par.peta p =>
    let bla := parTriangle p
    _ -- parTriangle p
  | .(_), Par.papp Par.pvar p2 => by
    simp [ucr]
    apply Par.papp
    apply parRefl
    apply parTriangle; apply p2
  | (app (lam t1) t2), Par.papp p1 p2 => _
  | (app (app t1 t2) t3), Par.papp p1 p2 => _
  | .(_), Par.plam p => _

def expand {Γ} (t : Term Γ) : Term Γ :=
  lam (app (rename Var.succ t) (var Var.zero))

def ucr2 {Γ} (t : Term Γ) : Term Γ :=
  expand (match t with
          | var x => var x
          | app (lam t1) t2 => subLast (ucr t1) (ucr t2)
          | lam t => lam (ucr t)
          | app t1 t2 => app (ucr t1) (ucr t2))

inductive Par2 : ∀{Γ}, Term Γ → Term Γ → Type   
| pvar : ∀{Γ} {x : Var Γ}, Par2 (var x) (var x)
| plam : ∀{Γ} {N N' : Term (succ Γ)},
  Par2 N N' → Par2 (lam N) (lam N')  
| papp : ∀{Γ}{L L' M M' : Term Γ},
  Par2 L L' → Par2 M M' → Par2 (app L M) (app L' M')   
| pbeta : ∀{Γ}{N N' : Term (succ Γ)} {M M' : Term Γ},
  Par2 N N' → Par2 M M' → Par2 (app (lam N) M) (subLast N' M')  
-- | peta : ∀{Γ} {M M' : Term Γ},
--   Par2 M M'
--   → Par2 M (lam (app (rename Var.succ M') (var Var.zero)))
| peta : ∀{Γ} {M M' : Term Γ},
  Par2 (lam (app (rename Var.succ M) (var Var.zero))) M'
  → Par2 M M' 

theorem par2Refl {Γ} {M : Term Γ} : Par2 M M := by
  induction M with
  | var i => apply Par2.pvar
  | app t1 t2 ih1 ih2 => apply Par2.papp; apply ih1; apply ih2
  | lam t ih => apply Par2.plam; apply ih

theorem renamePar2 {n1}
  {t1 t2 : Term n1} (step : Par2 t1 t2)
  : ∀ {n2} (ren : Ren n1 n2),
    Par2 (rename ren t1) (rename ren t2) := by sorry

theorem parTriangle2 {Γ} {M N : Term Γ} (step: Par2 M N) : Par2 N (ucr2 M) :=
  match step with
  | Par2.pvar => Par2.peta par2Refl
  | Par2.pbeta p1 p2 => _
  | Par2.peta p =>
    let bla := parTriangle2 p
    -- Par2.plam (Par2.papp (renamePar2 _ Var.succ) par2Refl) -- parTriangle p
    _
  | Par2.papp Par2.pvar p2 => _
  | Par2.papp (Par2.plam p) p2 => _
  | Par2.papp p1 p2 => _
  | Par2.plam p => _

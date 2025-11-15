-- This file is a translation of PLFA
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Tactic.Ring.RingNF

open Classical


inductive Constant
| strConst : String -> Constant

inductive Term : Type
| var : Nat → Term
| const : Constant → Term
| lam : String -> Term → Term
| app : Term → Term → Term

open Term

def lift (k : Nat) (t : Term) : Term :=
  match t with
  | var i => if i >= k then Term.var (Nat.succ i) else Term.var i
  | const c => const c
  | lam s t => lam s (lift (Nat.succ k) t)
  | app t1 t2 => app (lift k t1) (lift k t2)

def subst (k : Nat) (toSub : Term) (t : Term) : Term :=
  match t with
  | var i => if k < i then Term.var (Nat.pred i) else if i == k then toSub else Term.var i
  | const c => const c
  | lam s t => lam s (subst (Nat.succ k) (lift 0 toSub) t)
  | app t1 t2 => app (subst k toSub t1) (subst k toSub t2)

inductive Step : Term → Term → Prop where
| app1 : ∀{L L' M : Term},
    Step L L'
    → Step (app L M) (app L' M)
| app2 : ∀{L M M' : Term},
    Step M M'
    → Step (app L M) (app L M')
| beta : ∀ {s} {N : Term} {M : Term},
    Step (app (lam s N) M) (subst 0 N M)
| lam : ∀ {s} {N N' : Term},
    Step N N' → Step (lam s N) (lam s N')

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

theorem lift_lift (i1 i2 : Nat) (t : Term) :
    lift i1 (lift i2 t) =
      if i2 < i1
        then lift i2 (lift (Nat.pred i1) t)
        else lift (Nat.succ i2) (lift i1 t) := by
  revert i1 i2
  induction t with
  | var i =>
    intros
    repeat (first | simp [lift] | split | cutsat)
  | const c =>
    intros
    simp [lift]
  | lam s t ih =>
    intros
    simp [lift]
    rw [ih]
    simp
    repeat (first | simp | split | cutsat | contradiction)
  | app t1 t2 ih1 ih2 =>
    intros
    simp [lift]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)

theorem lift_subst (i1 i2 : Nat) (t1 t : Term) :
    lift i1 (subst i2 t1 t) =
      if i1 < i2
        then subst (Nat.succ i2) (lift i1 t1) (lift i1 t)
        else subst i2 (lift i1 t1) (lift (Nat.succ i1) t) := by
  revert i1 i2 t1
  induction t with
  | var i =>
    intros
    repeat (first | simp [subst, lift] | split | cutsat | contradiction)
  | const c =>
    intros
    simp [subst, lift]
  | lam s t ih =>
    intros
    simp [subst, lift]
    rw [ih]
    simp
    rw [lift_lift]
    repeat (first | simp | split | cutsat | contradiction)
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst, lift]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)

theorem subst_lift (i : Nat) (t1 t2 : Term) : subst i t1 (lift i t2) = t2 := by
  revert i t1
  induction t2 with
  | var i =>
    intros
    repeat (first | simp [subst, lift] | split | cutsat | contradiction)
  | const c =>
    intros
    simp [subst, lift]
  | lam s t ih =>
    intros
    simp [subst, lift]
    rw [ih]
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst, lift]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)

theorem subst_lift_off_by_1 (i : Nat) (t1 t : Term) :
    subst (i + 1) t1 (lift i t) = subst i t1 (lift (Nat.succ i) t) := by
  revert i t1
  induction t with
  | var i =>
    intros
    repeat' (first | simp [subst, lift] | split | cutsat | contradiction)
  | const c =>
    intros
    simp [subst, lift]
  | lam s t ih =>
    intros
    simp [subst, lift]
    rw [ih]
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst, lift]
    rw [ih1, ih2]
    repeat' (first | simp | split | cutsat | contradiction)


-- theorem lift_subst (i1 i2 : Nat) (t1 t : Term) :
--     (subst i1 t1 t (lift i2 t)) =
--       if i1 < i2
--         then subst (Nat.succ i2) (lift i1 t1) (lift i1 t)
--         else subst i2 (lift i1 t1) (lift (Nat.succ i1) t) := by

theorem subst_subst (i1 i2 : Nat) (t1 t2 t : Term) :
    subst i1 t1 (subst i2 t2 t) =
      if i1 < i2
      then subst (Nat.pred i2) (subst i1 t1 t2) (subst i1 (lift (Nat.pred i2) t1) t)
      else subst i2 (subst i1 t1 t2) (subst (Nat.succ i1) (lift i2 t1) t) := by
  revert i1 i2 t1 t2
  induction t with
  | var i =>
    intros
    repeat' (first | simp [subst] | split | cutsat | contradiction)
    . subst i
      sorry
    . repeat (first | simp [subst] | split | cutsat | contradiction)
    . repeat (first | simp [subst] | split | cutsat | contradiction)
    . sorry
  | const c =>
    intros
    simp [subst]
  | lam s t ih =>
    intros
    simp [subst]
    rw [ih]
    simp
    rw [lift_lift]
    rw [lift_subst]
    repeat (first | simp | split | cutsat | contradiction)
    . sorry
    . sorry
    . sorry
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)

--------------------------------------------------------------------------------
---------- A proof of confluence -----------------------------------------------
--------------------------------------------------------------------------------

inductive Par : Term → Term → Prop
| pvar : ∀{x : Nat}, Par (var x) (var x)
| pconst : ∀{c : Constant}, Par (const c) (const c)
| plam : ∀{s} {N N' : Term},
  Par N N' → Par (lam s N) (lam s N')
| papp : ∀{L L' M M' : Term},
  Par L L' → Par M M' → Par (app L M) (app L' M')
| pbeta : ∀{s} {N N' : Term} {M M' : Term},
  Par N N' → Par M M' → Par (app (lam s N) M) (subst 0 M' N')

theorem parRefl {t : Term} : Par t t := by
  induction t <;> constructor <;> repeat assumption

theorem parLift {i} {M M' : Term}
  (p : Par M M')
  : Par (lift i M) (lift i M') := by
  revert i
  induction p with
  | @pvar x => intros; simp [lift]; split<;> apply Par.pvar
  | pconst => intros; constructor
  | plam _p ih => intros; simp [lift]; apply Par.plam; apply ih
  | papp _p1 _p2 ih1 ih2 => intros; simp [lift]; apply (Par.papp ih1 ih2)
  | pbeta _p1 _p2 ih1 ih2 =>
    intros
    simp [lift]
    rw [lift_subst]
    apply Par.pbeta
    · apply ih1
    · apply ih2

theorem substPar {i} {N} {M M' : Term}
  (p : Par M M')
  : Par (subst i N M) (subst i N M') := by
  revert i N
  induction p with
  | @pvar x => intros; simp [subst]; split<;> apply parRefl
  | pconst => intros; constructor
  | plam _p ih => intros; simp [subst]; apply Par.plam; apply ih
  | papp _p1 _p2 ih1 ih2 => intros; simp [subst]; apply (Par.papp ih1 ih2)
  | pbeta _p1 _p2 ih1 ih2 =>
    intros
    simp [subst]
    rw [lift_subst]
    apply Par.pbeta
    · apply ih1
    · apply ih2

theorem substPar {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M M' : Term Γ}
  (ps : ParSubst sub1 sub2) (p : Par M M')
  : Par (subst sub1 M) (subst sub2 M') :=
  match p with
  | Par.pvar => ps
  | Par.pconst => by simp [subst]; constructor
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
  | const c => apply Par.pconst
  | app t1 t2 ih1 ih2 => apply Par.papp; apply ih1; apply ih2
  | lam s t ih => apply Par.plam; apply ih

-- While on paper the Takahashi method leads to a cleaner proof, in a theorem prover the proof
-- will be ugly either way and this way is shorter.
-- Also, using a takahashi function for beta-eta together seems to be very difficuly formally,
-- since the eta rule involves a substiution
theorem parDiamond {Γ} {t t1 t2 : Term Γ}
  (p1 : Par t t1) (p2 : Par t t2)
  : ∃ t', Par t1 t' ∧ Par t2 t' :=
  match p1, p2 with
  | Par.pvar, Par.pvar => ⟨_, Par.pvar, Par.pvar⟩
  | Par.pconst, Par.pconst => ⟨_, Par.pconst, Par.pconst⟩
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
    ⟨lam _ a, Par.plam pa1, Par.plam pa2⟩

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-------- Relations - from Nipkow (2001)
def Relation (A : Type) : Type := A → A → Prop

inductive Proof (P : Prop) : Type
| proof : P → Proof P

def closeRef {A} (R : Relation A) : Relation A :=
  fun x y => x = y ∨ R x y

def liftRef {A} {B} {R : Relation A} {R' : Relation B} {x y : A} (f : A → B)
  (ctr : ∀{x y}, R x y → R' (f x) (f y))
  : closeRef R x y → closeRef R' (f x) (f y) :=
  fun s => match s with
  | Or.inl rfl => Or.inl rfl
  | Or.inr s' => Or.inr (ctr s')

-- transitive relflexive closure of a relation
inductive closure {A} (R : Relation A) : A → A → Prop
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

inductive union {A} (R S : Relation A) : A → A → Prop
| r : ∀{x y}, R x y → union R S x y
| s : ∀{x y}, S x y → union R S x y

def liftUnion {A} {B} {R S : Relation A} {R' S' : Relation B} {x y : A} (f : A → B)
  (ctr1 : ∀{x y}, R x y → R' (f x) (f y))
  (ctr2 : ∀{x y}, S x y → S' (f x) (f y))
  : union R S x y → union R' S' (f x) (f y) :=
  fun s => match s with
  | union.r r => union.r (ctr1 r)
  | union.s s => union.s (ctr2 s)

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
def square {A} (R S T U : Relation A) : Prop :=
  {x y z : A} → R x y → S x z → ∃ u, T y u ∧ U z u

def commute {A} (R S : Relation A) : Prop := square R S S R
def diamond {A} (R : Relation A) : Prop := commute R R
def confluent {A} (R : Relation A) : Prop := diamond (closure R)

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
    | Or.inl p =>
      ⟨z, transitivity s (by rw [<- p]; exact x'z), closure.refl⟩
    | Or.inr r' =>
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

def dummy : ∀{Γ}, Term Γ := lam "x" (var Var.zero)

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
| lam : ∀ {Γ s} {N N' : Term (succ Γ)},
    StepEta N N' → StepEta (lam s N) (lam s N')
| eta : ∀{Γ s} {M : Term (succ Γ)},
 -- The idea to use subsitution here is from Nipkow 2001
  zFree M
  → StepEta (lam s (app M (var Var.zero))) (subLast M dummy)
| alpha : ∀{Γ s1 s2} {M : Term (succ Γ)},
  StepEta (lam s1 M) (lam s2 M)

theorem etaRename {Γ} {M M' : Term Γ}
  (p : StepEta M M')
  : ∀{Δ}, {ren : Ren Γ Δ} → StepEta (rename ren M) (rename ren M') := by
  induction p with
  | lam _p ih => intros; simp [rename]; apply StepEta.lam; apply ih
  | app1 _p ih => intros; simp [rename]; apply StepEta.app1; apply ih
  | app2 _p ih => intros; simp [rename]; apply StepEta.app2; apply ih
  | alpha => intros; simp [rename]; apply StepEta.alpha
  | @eta _ _ M zf => -- surely I could have written this proof better...
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

def EtaSubst {Γ} {Δ} (sub1 sub2 : Subst Γ Δ) : Prop :=
  {x : Var Γ} → closure StepEta (sub1 x) (sub2 x)

theorem closureEtaRename {Γ} {M M' : Term Γ}
  (p : closure StepEta M M')
  : ∀{Δ}, {ren : Ren Γ Δ} → closure StepEta (rename ren M) (rename ren M') :=
  match p with
  | closure.refl => closure.refl
  | closure.cons s ss => closure.cons (etaRename s) (closureEtaRename ss)

theorem etaSubstExts {Γ Δ} {sub1 sub2 : Subst Γ Δ}
  (ps : EtaSubst sub1 sub2)
  : EtaSubst (exts sub1) (exts sub2) := by
  intro x
  cases x
  . apply closure.refl
  . apply closureEtaRename; apply ps

theorem substEta {Γ Δ} {sub : Subst Γ Δ} {M M' : Term Γ}
  (p : StepEta M M')
  : StepEta (subst sub M) (subst sub M') :=
  match p with
  | StepEta.app1 p => StepEta.app1 (substEta p)
  | StepEta.app2 p => StepEta.app2 (substEta p)
  | StepEta.lam p => StepEta.lam (substEta p)
  | StepEta.alpha => StepEta.alpha
  | @StepEta.eta _ _ M zf => by
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

theorem substEta1 {Γ Δ} {sub1 sub2 : Subst Γ Δ} {M : Term Γ}
  (es : EtaSubst sub1 sub2)
  : closure StepEta (subst sub1 M) (subst sub2 M) :=
  match M with
  | var i => @es i
  | const c => by simp[subst]; constructor
  | app _t1 _t2 =>
    transitivity
      (liftCsr (fun x => app x _) StepEta.app1 (substEta1 es))
      (liftCsr (app _) StepEta.app2 (substEta1 es))
  | lam s _t => liftCsr (lam s) StepEta.lam (substEta1 (etaSubstExts es))

def etaSubstZero {Γ} {M M' : Term Γ}
  (p : closure StepEta M M') : EtaSubst (substZero M) (substZero M')
  := fun {x} =>
    match x with
    | Var.zero => p
    | Var.succ _x' => closure.refl

theorem subEta {Γ} {N N' : Term (succ Γ)} { M M' : Term Γ}
  (p1 : closure StepEta N N') (p2 : closure StepEta M M')
  : closure StepEta (subLast N M) (subLast N' M') :=
  match p1 with
  | closure.refl => substEta1 (etaSubstZero p2)
  | closure.cons s ss => closure.cons (substEta s) (subEta ss p2)

theorem lamRenFree {n2} {M : Term (succ n2)} {ren : Ren n1 n2}
  : renFree (ext ren) M ↔ renFree ren (lam s M) :=
    Iff.intro
      (fun ⟨t, renProof⟩ => ⟨lam s t, by simp [rename]; apply renProof⟩)
      (fun ⟨lam s' t, renProof⟩ => ⟨ t, by
        simp [rename] at renProof; cases renProof with | intro a b => subst a; assumption⟩)

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
  | StepEta.alpha => Iff.mp lamRenFree (Iff.mpr lamRenFree rf)

theorem stepZFree {n1 n2} {M N : Term n2} (step : Step M N) {ren : Ren n1 n2}
  (rf : renFree ren M) : renFree ren N :=
  match step with
  | Step.app1 p => Iff.mp appRenFree
    ⟨stepZFree p (And.left (Iff.mpr appRenFree rf))
    , (And.right (Iff.mpr appRenFree rf))⟩
  | Step.app2 p => Iff.mp appRenFree
    ⟨(And.left (Iff.mpr appRenFree rf))
    , stepZFree p (And.right (Iff.mpr appRenFree rf))⟩
  | Step.lam p => Iff.mp lamRenFree (stepZFree p (Iff.mpr lamRenFree rf))
  | Step.beta =>
    let ⟨rflamn, rfm⟩ := Iff.mpr appRenFree rf
    let rfn := Iff.mpr lamRenFree rflamn
    let ⟨m, proofm⟩ := rfm
    let ⟨n, proofn⟩ := rfn
    by
      --
      simp [renFree]
      exists (subLast n m)
      rw [<- proofm]
      rw [<- proofn]
      rw [renameSubstCommute]

theorem substStep {Γ Δ} {sub : Subst Γ Δ} {M M' : Term Γ}
  (step : Step M M')
  : Step (subst sub M) (subst sub M') :=
  match step with
  | Step.app1 p => Step.app1 (substStep p)
  | Step.app2 p => Step.app2 (substStep p)
  | Step.lam p => Step.lam (substStep p)
  | Step.beta => by
    simp [subst]
    rw [<- substCommute]
    apply Step.beta

-- def rfStepEta {Γ} := closeRef (@StepEta Γ)

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
    ⟨lam _ u, liftRef (lam _) StepEta.lam bla1, liftRef (lam _) StepEta.lam bla2⟩
  | StepEta.eta zf1, StepEta.eta zf2 => ⟨_, Or.inl rfl, Or.inl rfl⟩
  | StepEta.lam (StepEta.app1 s), StepEta.eta zf =>
    ⟨_, Or.inr (StepEta.eta (stepEtaZFree s zf)), Or.inr (substEta s)⟩
  | StepEta.eta zf, StepEta.lam (StepEta.app1 s) => -- REPEATED CASE
    ⟨_, Or.inr (substEta s), Or.inr (StepEta.eta (stepEtaZFree s zf))⟩
  | @StepEta.alpha _ _ s M, StepEta.alpha => ⟨lam s M, Or.inr StepEta.alpha, Or.inr StepEta.alpha⟩
  | StepEta.alpha, StepEta.lam s => ⟨_, Or.inr (StepEta.lam s), Or.inr StepEta.alpha⟩
  | StepEta.lam s, StepEta.alpha => ⟨_, Or.inr StepEta.alpha, Or.inr (StepEta.lam s)⟩
  | StepEta.alpha, StepEta.eta zf => ⟨_, Or.inr (StepEta.eta zf), Or.inl rfl⟩
  | StepEta.eta zf, StepEta.alpha => ⟨_, Or.inl rfl, Or.inr (StepEta.eta zf)⟩

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
      ⟨_, liftCsr (lam _) StepEta.lam q1,
        liftRef (lam _) Step.lam q2⟩
    | Step.app1 p1, StepEta.app2 p2 =>
      ⟨_, oneStep (StepEta.app2 p2),
        Or.inr (Step.app1 p1)⟩
    | Step.app2 p1, StepEta.app1 p2 => -- REPEATED CASE
      ⟨_, oneStep (StepEta.app1 p2)
          , Or.inr (Step.app2 p1)⟩
    | Step.beta, StepEta.app2 p => ⟨_, subEta closure.refl (oneStep p), Or.inr Step.beta⟩
    | Step.beta, StepEta.app1 (StepEta.lam p) => ⟨_, subEta (oneStep p) closure.refl, Or.inr Step.beta⟩
    | Step.beta, StepEta.app1 (StepEta.eta zf) => ⟨_, closure.refl, (by
        rw [subLastZFree (d1 := dummy)]
        apply Or.inl rfl
        apply zf
        )⟩
    | Step.lam (Step.app1 p), StepEta.eta zf => ⟨_, oneStep (StepEta.eta (stepZFree p zf)), Or.inr (substStep p)⟩
    | Step.lam Step.beta, @StepEta.eta _ _ (lam s a) zf =>
      ⟨_,
        oneStep (@StepEta.alpha _ _ s _),
        Or.inl (by
        apply Exists.elim; apply (Iff.mpr lamRenFree zf); intro t proof
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
        ))⟩
    | Step.beta, StepEta.app1 StepEta.alpha => ⟨_, closure.refl, Or.inr (Step.beta)⟩
    | Step.lam s, StepEta.alpha => ⟨_, oneStep StepEta.alpha, Or.inr (Step.lam s)⟩

--------------------------------------------------------------------------------
---------- Equivalence between Par and Step ------------------------------------
--------------------------------------------------------------------------------

theorem stepToPar {Γ} {t1 t2 : Term Γ}
  (step : Step t1 t2) : Par t1 t2 :=
  match step with
  | Step.app1 s => Par.papp (stepToPar s) parRefl
  | Step.app2 s => Par.papp parRefl (stepToPar s)
  | Step.lam s => Par.plam (stepToPar s)
  | Step.beta => Par.pbeta parRefl parRefl

theorem parToMultiStep {Γ} {t1 t2 : Term Γ}
  (par : Par t1 t2) : closure Step t1 t2 :=
  match par with
  | Par.pvar => closure.refl
  | Par.pconst => closure.refl
  | Par.papp p1 p2 => transitivity (liftCsr (fun x => app x _) Step.app1 (parToMultiStep p1))
    (liftCsr (app _) Step.app2 (parToMultiStep p2))
  | Par.plam s => liftCsr (lam _) Step.lam (parToMultiStep s)
  | Par.pbeta s1 s2 => -- Can I do this case without proving substitution properties of MultiStep?
    transitivity (transitivity
      (liftCsr (fun x => app (lam _ x) _) (Step.app1 ∘ Step.lam) (parToMultiStep s1))
      (liftCsr (app _) Step.app2 (parToMultiStep s2)))
      (oneStep Step.beta)

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

--------------------------------------------------------------------------------
---------- Collecting all of the theorems together into confluence -------------
--------------------------------------------------------------------------------

theorem diamondToProperty {A} {R : Relation A}
  (d : diamond R)
  : square R R (closure R) (closeRef R) :=
  fun s1 s2 =>
    let ⟨_, s2', s1'⟩ := d s1 s2
    ⟨_, oneStep s2', Or.inr s1'⟩
theorem parConfluent {Γ} : confluent (@Par Γ) :=
  commutationLemma (diamondToProperty parDiamond)
theorem stepConfluent {Γ} : confluent (@Step Γ) :=
  fun s1 s2 =>
    let ⟨_, s2', s1'⟩ := parConfluent (multiStepToMultiPar s1) (multiStepToMultiPar s2)
    ⟨_, multiParToMultiStep s2', multiParToMultiStep s1'⟩

theorem closeRefToClosure {A} {R : Relation A}
  {x y}
  (r : closeRef R x y) : closure R x y :=
  match r with
  | Or.inl rfl => closure.refl
  | Or.inr r => oneStep r

theorem propertyToProperty {A} {R : Relation A}
  (sq : square R R (closeRef R) (closeRef R))
  : square R R (closure R) (closeRef R) :=
  fun s1 s2 =>
    let ⟨_, s2', s1'⟩ := sq s1 s2
    ⟨_, closeRefToClosure s2', s1'⟩

theorem etaConfluent {Γ} : confluent (@StepEta Γ) :=
  commutationLemma (propertyToProperty etaProperty)

def AllStep {Γ} : Relation (Term Γ) := closure (union Step StepEta)

theorem confluence {Γ} : confluent (union (@Step Γ) StepEta) :=
  commutativeUnion stepConfluent etaConfluent (commutationLemma betaEtaCommuteProperty)

---------------- definitions to be used in the quotient --------------

def singleLift {Γ} (i : Var (succ Γ)) : Ren Γ (succ Γ) :=
  match Γ, i with
  | _, Var.zero => Var.succ
  | Nat.succ Γ', Var.succ i' => ext (singleLift i')

def lift {Γ} (i : Var (succ Γ)) (t : Term Γ) : Term (succ Γ) :=
  rename (singleLift i) t

theorem lift_app {Γ} {t1 t2 : Term Γ} (i : Var (succ Γ))
  : lift i (app t1 t2) = app (lift i t1) (lift i t2) := by
  simp [lift, rename]

theorem lift_lam {Γ s} {t : Term (succ Γ)} (i : Var (succ Γ))
  : lift i (lam s t) = lam s (lift (Var.succ i) t) := by
  simp [lift, rename, singleLift]

-- something for var?
-- def singleSub {Γ} (i : Var (succ Γ)) (toSub : Term Γ) : Subst (succ Γ) Γ :=

deriving instance BEq for Var

-- is there really NO simple recursive definition?
def singleSub' {Γ Γ'} (r : Ren (succ Γ) Γ') (i : Var (succ Γ)) (toSub : Term Γ') : Subst (succ Γ) Γ' :=
  match Γ, i with
  | _, Var.zero => cons toSub _
  | Nat.succ Γ', Var.succ i' =>
    let x := singleSub i' toSub
    _

def singleSub {Γ} (i : Var (succ Γ)) (toSub : Term Γ) : Subst (succ Γ) Γ :=
  fun i' =>
    if i == i'
      then toSub
      else _
  -- match Γ, i with
  -- | _, Var.zero => _-- cons toSub ids
  -- | Nat.succ Γ2, Var.succ i' => cons _ (singleSub' i' toSub)

#check Term
def sub : ∀{Γ}, Term Γ → Var Γ → Term Γ → Term Γ :=
  fun t x toSub => subst _ t

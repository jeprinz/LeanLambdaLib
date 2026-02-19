-- this file is a proof of confluence of lambda-beta-eta
-- i very roughly followed Nipkow (2001), although i did many parts differently

import Mathlib.Tactic.ApplyFun

namespace SynTerm

inductive Constant
| strConst : String -> Constant
| natConst : Nat → Constant

inductive Term : Type
| var : Nat → Term
| const : Constant → Term
| lam : String -> Term → Term
| app : Term → Term → Term

open Term

def lift (k : Nat) (t : Term) : Term :=
  match t with
  | var i => Term.var (if i >= k then Nat.succ i else i)
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
    Step (app (lam s N) M) (subst 0 M N)
| lam : ∀ {s} {N N' : Term},
    Step N N' → Step (lam s N) (lam s N')

-------------------------------------------------------------------------------------
-- everyone's favorite part of these kind of proofs : a bzillion subst/lift lemmas --
-------------------------------------------------------------------------------------

-- my strategy picking these lemmas is: they are those necessary to bring expressions
-- to a normal form where all lifts are inside substs, lifts are in decreasing index order,
-- substs are in increasing index order, and also any further lemmas that ended up being necessary

theorem lift_lift (i1 i2 : Nat) (t : Term) (H : i2 < i1) :
    lift i1 (lift i2 t) = lift i2 (lift (Nat.pred i1) t) := by
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
    rw [ih] <;> try cutsat
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

theorem subst_lift_off_by_1 (i1 i2 : Nat) (t1 t : Term) (H : i1 = i2 + 1) :
    subst i1 t1 (lift i2 t) = subst i2 t1 (lift i1 t) := by
  revert i1 i2 H t1
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
    cutsat
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst, lift]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)


theorem subst_subst (i1 i2 : Nat) (t1 t2 t : Term) (H : i1 >= i2) :
    subst i1 t1 (subst i2 t2 t) =
      subst i2 (subst i1 t1 t2) (subst (Nat.succ i1) (lift i2 t1) t) := by
  revert i1 i2 t1 t2
  induction t with
  | var i =>
    intros
    repeat' (first | simp [subst] | split | cutsat | contradiction | rw [subst_lift])
  | const c =>
    intros
    simp [subst]
  | lam s t ih =>
    intros
    simp [subst]
    rw [ih] <;> try cutsat
    simp
    rw [lift_lift] <;> try cutsat
    rw [lift_subst]
    repeat' (first | simp | split | cutsat )
    rewrite [subst_lift_off_by_1] <;> cutsat
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)

theorem lift_injective {i : Nat} {M N : Term} (H : lift i M = lift i N) : M = N := by
  revert i N H
  induction M with
  | var i =>
    intros i N H
    cases N <;> try contradiction
    simp [lift] at H
    repeat' (first | split at H | cutsat)
  | const c =>
    intros i N H
    cases N <;> try contradiction
    simp [lift] at H
    subst c
    rfl
  | lam s t ih =>
    intros i N H
    cases N <;> try contradiction
    simp [lift] at H
    cases H with | intro H1 H2
    subst s
    rw [ih H2]
  | app t1 t2 ih1 ih2 =>
    intros i N H
    cases N <;> try contradiction
    simp [lift] at H
    cases H with | intro H1 H2
    rw [ih1 H1]
    rw [ih2 H2]

theorem subst_lift_2 (i : Nat) {t : Term} :
    t = subst i (var i) (lift (Nat.succ i) t) := by
  revert i
  induction t with
  | var i =>
    intros i
    simp [subst, lift]
    repeat' (first | split | cutsat )
  | const c =>
    intros i
    rfl
  | lam s t ih =>
    intros i
    simp [lift, subst]
    apply ih (Nat.succ i)
  | app t1 t2 ih1 ih2 =>
    intros i
    simp [subst, lift]
    apply And.intro
    · apply ih1
    · apply ih2

theorem subst_subst_2 (i1 i2 : Nat) (t1 t2 t : Term) (H : i1 < i2) :
    subst i1 t1 (subst i2 t2 t) =
      subst i2.pred (subst i1 t1 t2) (subst i1 (lift i2.pred t1) t) := by
  revert i1 i2 t1 t2
  induction t with
  | var i =>
    intros
    repeat' (first | simp [subst] | split | cutsat | contradiction | rw [subst_lift])
  | const c =>
    intros
    simp [subst]
  | lam s t ih =>
    intros
    simp [subst]
    rw [ih] <;> try cutsat
    simp
    rw [lift_lift] <;> try cutsat
    rw [lift_subst]
    repeat' (first | simp | split | cutsat )
    rewrite [subst_lift_off_by_1] <;> cutsat
  | app t1 t2 ih1 ih2 =>
    intros
    simp [subst]
    rw [ih1, ih2]
    repeat (first | simp | split | cutsat | contradiction)

--------------------------------------------------------------------------------
---------- A proof of confluence for beta alone without eta -------------------
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

theorem parSubst {i} {N N'} {M M' : Term}
  (p1 : Par N N')
  (p2 : Par M M')
  : Par (subst i N M) (subst i N' M') := by
  revert i N N'
  induction p2 with
  | @pvar x =>
    intros; simp [subst]; split
    · apply parRefl
    · split
      · assumption
      · apply parRefl
  | pconst => intros; constructor
  | plam _p ih =>
    intros i N N' pNN'
    simp [subst]; apply Par.plam; apply ih
    apply parLift
    apply pNN'
  | papp _p1 _p2 ih1 ih2 =>
    intros i N N' pNN'
    simp [subst]; apply (Par.papp (ih1 pNN') (ih2 pNN'))
  | @pbeta s a a' b b' _p1 _p2 ih1 ih2 =>
    intros i N N' pNN'
    rw [subst_subst] <;> try cutsat
    simp [subst]
    apply Par.pbeta
    · apply (ih1 (parLift pNN'))
    · apply (ih2 pNN')

theorem parDiamond {t t1 t2 : Term}
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
    ⟨subst 0 b a, parSubst pb1 pa1, parSubst pb2 pa2⟩
    -- ⟨subst 0 b a, _, _⟩
  | Par.papp (Par.plam a1) b1, Par.pbeta a2 b2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subst 0 b a, Par.pbeta pa1 pb1, parSubst pb2 pa2⟩
  | Par.pbeta a1 b1, Par.papp (Par.plam a2) b2 => -- REPEATED CASE
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    let ⟨b, pb1, pb2⟩ := parDiamond b1 b2
    ⟨subst 0 b a, parSubst pb1 pa1, Par.pbeta pa2 pb2⟩
  | Par.plam a1, Par.plam a2 =>
    let ⟨a, pa1, pa2⟩ := parDiamond a1 a2
    ⟨lam _ a, Par.plam pa1, Par.plam pa2⟩

--------------------------------------------------------------------------------
------- some general facts about relations - from Nipkow (2001) ----------------
--------------------------------------------------------------------------------
def Relation (A : Type) : Type := A → A → Prop

inductive Proof (P : Prop) : Type
| proof : P → Proof P

def closeRef {A} (R : Relation A) : Relation A :=
  fun x y => x = y ∨ R x y

def liftRef {A} {B} {R : Relation A} {R' : Relation B} {x y : A} (f : A → B)
  (ctr : ∀ {x y}, R x y → R' (f x) (f y))
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

def closureClosure {A} {R : Relation A} {x y : A} (H : closure (closure R) x y)
  : closure R x y :=
  match H with
  | .refl => closure.refl
  | .cons a b => transitivity a (closureClosure b)

def liftCsr {A} {B} {R : Relation A} {R' : Relation B} {x y : A} (f : A → B)
  (ctr : ∀ {x y}, R x y → R' (f x) (f y))
  : closure R x y → closure R' (f x) (f y) :=
  fun s => match s with
  | closure.refl => closure.refl
  | closure.cons xy yz => closure.cons (ctr xy) (liftCsr f ctr yz)

def liftCsr2 {A} {B} {R : Relation A} {R' : Relation B} {x y x' y' : A} (f : A → A → B)
  (ctr1 : ∀ {x x' y : A}, R x x' → R' (f x y) (f x' y))
  (ctr2 : ∀ {x y y' : A}, R y y' → R' (f x y) (f x y'))
  : closure R x x' → closure R y y' → closure R' (f x y) (f x' y') :=
  fun s1 s2 => match s1, s2 with
  | closure.refl, s2 => liftCsr _ ctr2 s2
  | closure.cons xy yz, s2 =>
    closure.cons (ctr1 xy) (liftCsr2 f ctr1 ctr2 yz s2)

inductive union {A} (R S : Relation A) : A → A → Prop
| r : ∀{x y}, R x y → union R S x y
| s : ∀{x y}, S x y → union R S x y

def liftUnion {A} {B} {R S : Relation A} {R' S' : Relation B} {x y : A} (f : A → B)
  (ctr1 : ∀ {x y}, R x y → R' (f x) (f y))
  (ctr2 : ∀ {x y}, S x y → S' (f x) (f y))
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

---------------------------------------------------------------------------------
------- Eta ---------------------------------------------------------------------
---------------------------------------------------------------------------------

def dummy : Term := const (Constant.strConst "dummy")

inductive StepEta : Term → Term → Prop where
| app1 : ∀ {L L' M : Term},
    StepEta L L'
    → StepEta (app L M) (app L' M)
| app2 : ∀ {L M M' : Term},
    StepEta M M'
    → StepEta (app L M) (app L M')
| lam : ∀ {s} {N N' : Term},
    StepEta N N' → StepEta (lam s N) (lam s N')
| eta : ∀{s} {M M' : Term},
  M = lift 0 M'
  → StepEta (lam s (app M (var 0))) M'
| alpha : ∀{s1 s2} {M : Term},
  StepEta (lam s1 M) (lam s2 M)


theorem etaLift {i} {M M' : Term}
  (p : StepEta M M')
  : StepEta (lift i M) (lift i M') := by
  revert i
  induction p with
  | lam _p ih => intros; simp [lift]; apply StepEta.lam; apply ih
  | app1 _p ih => intros; simp [lift]; apply (StepEta.app1 ih)
  | app2 _p ih => intros; simp [lift]; apply (StepEta.app2 ih)
  | @eta s M M' p =>
    intros
    subst M
    simp [lift]
    rw [lift_lift] <;> try cutsat
    apply StepEta.eta
    rfl
  | alpha =>
    intros
    apply StepEta.alpha

theorem liftStep {i} {M M' : Term}
  (step : Step M M')
  : Step (lift i M) (lift i M') :=
  match step with
  | Step.app1 p => Step.app1 (liftStep p)
  | Step.app2 p => Step.app2 (liftStep p)
  | Step.lam p => Step.lam (liftStep p)
  | Step.beta => by
    simp [lift]
    rw [lift_subst]
    apply Step.beta

theorem etaSubst1 {i} {N N'} {M : Term}
  (p : StepEta N N')
  : closure StepEta (subst i N M) (subst i N' M) :=
  match M with
  | var i => by
    repeat' (first | simp [subst] | split | cutsat | apply closure.refl)
    apply oneStep
    assumption
  | const c => closure.refl
  | lam s t => liftCsr (lam _) StepEta.lam (etaSubst1 (etaLift p))
  | app t1 t2 => transitivity
    (liftCsr (fun x => app x _) StepEta.app1 (etaSubst1 p))
    (liftCsr (app _) StepEta.app2 (etaSubst1 p))

theorem etaSubst2 (i N) {M M' : Term}
  (p : StepEta M M')
  : StepEta (subst i N M) (subst i N M') :=
  match p with
  | .app1 p => StepEta.app1 (etaSubst2 i N p)
  | .app2 p => StepEta.app2 (etaSubst2 i N p)
  | .lam p => StepEta.lam (etaSubst2 _ _ p)
  | .alpha => StepEta.alpha
  | @StepEta.eta s M M' p => by
    subst M
    simp [subst]
    have iamwritingaproof : subst (i + 1) (lift 0 N) (lift 0 M') = lift 0 (subst i N M') := by
      rewrite [lift_subst]
      split <;> try cutsat
      rewrite [subst_lift_off_by_1] <;> try cutsat
    rewrite [iamwritingaproof]
    apply StepEta.eta
    rfl

theorem substStep2 (i N) {M M' : Term}
  (step : Step M M')
  : Step (subst i N M) (subst i N M') :=
  match step with
  | Step.app1 p => Step.app1 (substStep2 i N p)
  | Step.app2 p => Step.app2 (substStep2 i N p)
  | Step.lam p => Step.lam (substStep2 _ _ p)
  | Step.beta => by
    simp [subst]
    rw [subst_subst] <;> try cutsat
    apply Step.beta

theorem substStep1 {i} {N N'} {M : Term}
  (p : Step N N')
  : closure Step (subst i N M) (subst i N' M) :=
  match M with
  | var i => by
    repeat' (first | simp [subst] | split | cutsat | apply closure.refl)
    apply oneStep
    assumption
  | const c => closure.refl
  | lam s t => liftCsr (lam _) Step.lam (substStep1 (liftStep p))
  | app t1 t2 => transitivity
    (liftCsr (fun x => app x _) Step.app1 (substStep1 p))
    (liftCsr (app _) Step.app2 (substStep1 p))
 --
theorem stepEtaRespectsLift {i : Nat} {M N : Term}
  (step : StepEta (lift i M) N)
  : exists N', N = lift i N' := by
  generalize H : lift i M = x at *
  revert i M
  induction step with
  | lam _p ih =>
    intros i M H
    cases M with | lam s t => _ | _ <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    specialize (ih rfl)
    rcases ih with ⟨N', rfl⟩
    exists (lam s N')
  | @app1 L L' R _p1 ih =>
    intros i M H
    cases M <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    specialize (ih rfl)
    rcases ih with ⟨N', rfl⟩
    exact ⟨app _ _, rfl⟩
  | app2 _p1 ih =>
    intros i M H
    cases M <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    specialize (ih rfl)
    rcases ih with ⟨N', rfl⟩
    exact ⟨app _ _, rfl⟩
  | alpha =>
    intros i M H
    cases M with | lam s t => _ | _ <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    exact ⟨lam _ t, rfl⟩
  | @eta s M M' p =>
    intros i M' H
    subst M
    cases M' with | lam s t => _ | _  <;> simp [lift] at H
    rcases H with ⟨rfl, H⟩
    cases t with | app l r => _ | _  <;> simp [lift] at H
    rcases H with ⟨q, H⟩
    clear H
    apply_fun (subst 0 (lift i dummy)) at q
    rewrite [subst_lift] at q
    have coolfact : subst 0 (lift i dummy) (lift (i + 1) l) = lift i (subst 0 dummy l) := by
      rw [lift_subst]
      simp -- TODO: how does simp solve this goal?
    rewrite [coolfact] at q
    exists (subst 0 dummy l)
    subst M'
    rfl

theorem stepRespectsLift {i : Nat} {M N : Term}
  (step : Step (lift i M) N)
  : exists N', N = lift i N' := by
  generalize H : lift i M = x at *
  revert i M
  induction step with
  | lam _p ih =>
    intros i M H
    cases M with | lam s t => _ | _ <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    specialize (ih rfl)
    rcases ih with ⟨N', rfl⟩
    exists (lam s N')
  | @app1 L L' R _p1 ih =>
    intros i M H
    cases M <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    specialize (ih rfl)
    rcases ih with ⟨N', rfl⟩
    exact ⟨app _ _, rfl⟩
  | app2 _p1 ih =>
    intros i M H
    cases M <;> simp [lift] at H
    rcases H with ⟨rfl, rfl⟩
    specialize (ih rfl)
    rcases ih with ⟨N', rfl⟩
    exact ⟨app _ _, rfl⟩
  | beta =>
    intros i M H
    cases M with simp [lift] at H | app l r => _
    rcases H with ⟨H, rfl⟩
    cases l with simp [lift] at H | lam s t => _
    rcases H with ⟨rfl, rfl⟩
    exists (subst 0 r t)
    rw [lift_subst]
    split; try cutsat
    rfl

theorem etaProperty : square StepEta StepEta
  (closeRef StepEta) (closeRef StepEta) :=
  fun p1 p2 =>
  match p1, p2 with
  | StepEta.app1 s1, StepEta.app1 s2 =>
    let ⟨u, bla1, bla2⟩ := etaProperty s1 s2
    ⟨app u _, liftRef (fun x => app x _) StepEta.app1 bla1,
      liftRef (fun x => app x _) StepEta.app1 bla2⟩
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
  | StepEta.eta p, StepEta.eta p' =>
    ⟨_, Or.inl rfl, Or.inl (lift_injective (Eq.trans (Eq.symm p') p)) ⟩
  | StepEta.lam (StepEta.app1 s), StepEta.eta p => by
    subst_vars
    have s' := etaSubst2 0 dummy s
    have ⟨N', p⟩ := stepEtaRespectsLift s
    subst_vars
    rw [subst_lift] at s'
    refine ⟨_, Or.inr (StepEta.eta ?_), Or.inr s'⟩
    rw [subst_lift]
  | StepEta.eta p, StepEta.lam (StepEta.app1 s) => by -- REPEATED CASE
    subst_vars
    have s' := etaSubst2 0 dummy s
    have ⟨N', p⟩ := stepEtaRespectsLift s
    subst_vars
    rw [subst_lift] at s'
    refine ⟨_, Or.inr s', Or.inr (StepEta.eta ?_)⟩
    rw [subst_lift]
  | @StepEta.alpha _ s M, StepEta.alpha => ⟨lam s M, Or.inr StepEta.alpha, Or.inr StepEta.alpha⟩
  | StepEta.alpha, StepEta.lam s => ⟨_, Or.inr (StepEta.lam s), Or.inr StepEta.alpha⟩
  | StepEta.lam s, StepEta.alpha => ⟨_, Or.inr StepEta.alpha, Or.inr (StepEta.lam s)⟩
  | StepEta.alpha, StepEta.eta p =>
    ⟨_, Or.inr (StepEta.eta p), Or.inl rfl⟩
  | StepEta.eta p, StepEta.alpha => -- REPEATED CASE
    ⟨_, Or.inl rfl, Or.inr (StepEta.eta p)⟩

theorem betaEtaCommuteProperty
  : square Step StepEta (closure StepEta) (closeRef Step) :=
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
    | Step.beta, StepEta.app2 p => ⟨_, etaSubst1 p, Or.inr Step.beta⟩
    | Step.beta, StepEta.app1 (StepEta.lam p) =>
      -- ⟨_, subEta (oneStep p) closure.refl, Or.inr Step.beta⟩
      ⟨_, oneStep (etaSubst2 _ _ p), Or.inr Step.beta⟩
    | Step.beta, StepEta.app1 (StepEta.eta zf) => ⟨_, closure.refl, (by
        subst_vars
        simp [subst]
        rw [subst_lift]
        apply Or.inl rfl
        )⟩
    | Step.lam (Step.app1 s), StepEta.eta zf => by
      subst_vars
      have s' := substStep2 0 dummy s
      have ⟨N', p⟩ := stepRespectsLift s
      subst_vars
      rw [subst_lift] at s'
      refine ⟨_, oneStep (StepEta.eta ?_), Or.inr s'⟩
      rw [subst_lift]
    | Step.lam Step.beta, @StepEta.eta _ _ (lam s a) zf =>
      ⟨_,
        oneStep (@StepEta.alpha _ s _),
        Or.inl (by
        --
        simp [lift] at zf
        rcases zf with ⟨rfl, rfl⟩
        simp
        apply subst_lift_2
        )⟩
    | Step.beta, StepEta.app1 StepEta.alpha => ⟨_, closure.refl, Or.inr (Step.beta)⟩
    | Step.lam s, StepEta.alpha => ⟨_, oneStep StepEta.alpha, Or.inr (Step.lam s)⟩

--------------------------------------------------------------------------------
---------- Equivalence between Par and Step ------------------------------------
--------------------------------------------------------------------------------

theorem stepToPar {t1 t2 : Term}
  (step : Step t1 t2) : Par t1 t2 :=
  match step with
  | Step.app1 s => Par.papp (stepToPar s) parRefl
  | Step.app2 s => Par.papp parRefl (stepToPar s)
  | Step.lam s => Par.plam (stepToPar s)
  | Step.beta => Par.pbeta parRefl parRefl

theorem parToMultiStep {t1 t2 : Term}
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

theorem multiParToMultiStep {t1 t2 : Term}
  (par : closure Par t1 t2) : closure Step t1 t2 :=
  match par with
  | closure.refl => closure.refl
  | closure.cons s ss => transitivity (parToMultiStep s) (multiParToMultiStep ss)

theorem multiStepToMultiPar {t1 t2 : Term}
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
theorem parConfluent : confluent Par :=
  commutationLemma (diamondToProperty parDiamond)
theorem stepConfluent : confluent Step :=
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

theorem etaConfluent : confluent StepEta :=
  commutationLemma (propertyToProperty etaProperty)

def AllStep : Relation Term := closure (union Step StepEta)

theorem confluence : confluent (union Step StepEta) :=
  commutativeUnion stepConfluent etaConfluent (commutationLemma betaEtaCommuteProperty)

---------------- definitions to be used in the quotient --------------

def equiv (t1 t2 : Term) := ∃ t, AllStep t1 t /\ AllStep t2 t

-- lifts from empty context to any context
def liftMulti (n : Nat) (t : Term) : Term :=
  match n with
  | .zero => t
  | .succ n' => lift 0 (liftMulti n' t)

theorem liftMultiStep {i} {M M' : Term}
  (step : Step M M')
  : Step (liftMulti i M) (liftMulti i M') :=
  match i with
  | .zero => step
  | .succ i' => liftStep (@liftMultiStep i' _ _ step)

theorem liftMultiStepEta {i} {M M' : Term}
  (step : StepEta M M')
  : StepEta (liftMulti i M) (liftMulti i M') :=
  match i with
  | .zero => step
  | .succ i' => etaLift (@liftMultiStepEta i' _ _ step)

theorem liftLiftMulti (n i : Nat) (H : i ≤ n) (t : Term)
  : lift i (liftMulti n t) = liftMulti (Nat.succ n) t := by
  revert i t
  induction n with
  | zero =>
    intros i H t
    cases H
    rfl
  | succ n ih =>
    intros i H t
    simp [liftMulti]
    cases i with
    | zero => rfl
    | succ i' =>
      rw [lift_lift] <;> try cutsat
      simp at *
      rw [ih _ H]
      rfl

theorem substLiftMulti (n i : Nat) (t1 t2 : Term) (H : i < n)
  : subst i t1 (liftMulti n t2) = liftMulti (Nat.pred n) t2 := by
  cases n with
  | zero =>
    cases H
  | succ n' =>
    rw [<- liftLiftMulti n' i] <;> try cutsat
    rw [subst_lift]
    rfl

lemma constStep' {c t} (step : (union Step StepEta) (const c) t) : t = const c := by
  cases step with
  | r step => cases step -- TODO: i don't know how cases solves this goal
  | s step => cases step

theorem constStep {c t} (step : AllStep (const c) t) : t = const c := by
  generalize eqn : (const c) = t1 at *
  induction step with
  | refl => rfl
  | cons s ss ih =>
    subst_vars
    have s := constStep' s
    subst_vars
    apply ih
    rfl

lemma varStep' {i t} (step : (union Step StepEta) (var i) t) : t = var i := by
  cases step with
  | r step => cases step -- TODO: i don't know how cases solves this goal
  | s step => cases step

theorem varStep {i t} (step : AllStep (var i) t) : t = var i := by
  generalize eqn : (var i) = t1 at *
  induction step with
  | refl => rfl
  | cons s ss ih =>
    subst_vars
    have s := varStep' s
    subst_vars
    apply ih
    rfl

theorem liftMultiLiftMulti {n m} {t : Term}
  : liftMulti n (liftMulti m t) = liftMulti (n + m) t := by
  induction n with
  | zero => simp [liftMulti]
  | succ n ih =>
    simp [liftMulti, ih]
    have h : n + 1 + m = (n + m).succ := by grind
    rw [h]
    simp [liftMulti]

end SynTerm

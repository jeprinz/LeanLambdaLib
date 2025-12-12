import LambdaLib.term
import Qq
import Lean

open Lean hiding Term
open Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

namespace QuotTerm
open SynTerm

instance Term.equivalence : Equivalence equiv where
  refl := by
    intros t
    exists t
    apply And.intro
    · apply closure.refl
    · apply closure.refl
  symm := by
    intros a b e
    rcases e with ⟨t, r1, r2⟩
    exact ⟨t, r2, r1⟩
  trans := by
    intros a b c e1 e2
    rcases e1 with ⟨t1, r1, r2⟩
    rcases e2 with ⟨t2, r3, r4⟩
    have ⟨t, r5, r6⟩ := confluence r2 r3
    exact ⟨t, transitivity r1 r5, transitivity r4 r6⟩

instance Term.setoid : Setoid Term where
  r := equiv
  iseqv := Term.equivalence

def QTerm := Quotient Term.setoid

theorem liftClosureUnion (f : Term → Term)
  (respectStep : ∀ {x y}, Step x y → Step (f x) (f y))
  (respectEta : ∀ {x y}, StepEta x y → StepEta (f x) (f y))
  : ∀{x y}, AllStep x y → AllStep (f x) (f y) := by
  intros x y eq
  refine (liftCsr f ?_ eq)
  intros x y step
  exact (liftUnion f respectStep respectEta step)

theorem respectStepLemma (f : Term → Term)
  (respectStep : ∀ {x y}, Step x y → Step (f x) (f y))
  (respectEta : ∀ {x y}, StepEta x y → StepEta (f x) (f y))
  : ∀⦃x y⦄, x ≈ y → f x ≈ f y := by
  intros x y eq
  rcases eq with ⟨t, ⟨l, r⟩⟩
  have l' := liftClosureUnion f respectStep respectEta l
  have r' := liftClosureUnion f respectStep respectEta r
  exact ⟨f t, ⟨l', r'⟩⟩

theorem respectClosureUnion2 (f : Term → Term → Term)
  (respectStep1 : ∀ {y x x'}, Step x x' → closure Step (f x y) (f x' y))
  (respectEta1 : ∀ {y x x'}, StepEta x x' → closure StepEta (f x y) (f x' y))
  (respectStep2 : ∀ {x y y'}, Step y y' → closure Step (f x y) (f x y'))
  (respectEta2 : ∀ {x y y'}, StepEta y y' → closure StepEta (f x y) (f x y'))
  : ∀{x x' y y'}, AllStep x x' → AllStep y y' → AllStep (f x y) (f x' y') := by
  intros x x' y y' eqx eqy
  apply closureClosure
  refine (liftCsr2 f ?_ ?_ eqx eqy)
  · intros x x' y step
    exact (unionClosureToClosureUnion (liftUnion (fun x => f x y) respectStep1 respectEta1 step))
  · intros x x' y step
    exact (unionClosureToClosureUnion (liftUnion (f x) respectStep2 respectEta2 step))

theorem respectStepLemma2 (f : Term → Term → Term)
  (respectStep1 : ∀ {y x x'}, Step x x' → closure Step (f x y) (f x' y))
  (respectEta1 : ∀ {y x x'}, StepEta x x' → closure StepEta (f x y) (f x' y))
  (respectStep2 : ∀ {x y y'}, Step y y' → closure Step (f x y) (f x y'))
  (respectEta2 : ∀ {x y y'}, StepEta y y' → closure StepEta (f x y) (f x y'))
  : ∀⦃x x'⦄, x ≈ x' → ∀⦃y y'⦄, y ≈ y' → f x y ≈ f x' y' := by
  intros x x' eqx y y' eqy
  rcases eqx with ⟨tx, ⟨lx, rx⟩⟩
  rcases eqy with ⟨ty, ⟨ly, ry⟩⟩
  have l' := respectClosureUnion2 f respectStep1 respectEta1 respectStep2 respectEta2 lx ly
  have r' := respectClosureUnion2 f respectStep1 respectEta1 respectStep2 respectEta2 rx ry
  exact ⟨f tx ty, ⟨l', r'⟩⟩

-----------------------------------------------------------------------------
---- define the main constructions of quotiented terms ----------------------
-----------------------------------------------------------------------------

@[irreducible]
def lam (s : String) (t : QTerm) : QTerm :=
  Quotient.map (Term.lam s) (respectStepLemma (Term.lam s) Step.lam StepEta.lam) t

@[irreducible]
def app (t1 t2 : QTerm) : QTerm :=
  Quotient.map₂ Term.app
    (respectStepLemma2 Term.app (oneStep ∘ Step.app1) (oneStep ∘ StepEta.app1)
      (oneStep ∘ Step.app2) (oneStep ∘ StepEta.app2)) t1 t2

@[irreducible]
def var (i : Nat) : QTerm := Quotient.mk _ (Term.var i)

@[irreducible]
def const (c : Constant) : QTerm := Quotient.mk _ (Term.const c)

@[irreducible]
def lift (i : Nat) (t : QTerm) : QTerm :=
  Quotient.map (SynTerm.lift i) (respectStepLemma (SynTerm.lift i) liftStep etaLift) t

@[irreducible]
def subst (i : Nat) (t1 t2 : QTerm) : QTerm :=
  Quotient.map₂ (SynTerm.subst i)
    (respectStepLemma2 (SynTerm.subst i) substStep1 etaSubst1
      (oneStep ∘ substStep2 _ _) (oneStep ∘ etaSubst2 _ _)) t1 t2

@[irreducible]
def liftMulti (i : Nat) (t : QTerm) : QTerm :=
  Quotient.map (SynTerm.liftMulti i) (respectStepLemma (SynTerm.liftMulti i)
  liftMultiStep liftMultiStepEta) t

-----------------------------------------------------------------------------
---- equations over quotiented terms ----------------------------------------
-----------------------------------------------------------------------------

theorem lift_app {i t1 t2}
  : lift i (app t1 t2) = app (lift i t1) (lift i t2) := by
  apply Quotient.ind _ t1
  apply Quotient.ind _ t2
  intros
  simp [lift, app, SynTerm.lift]

theorem lift_lam {i s t} : lift i (lam s t) = lam s (lift (Nat.succ i) t) := by
  apply Quotient.ind _ t
  intros
  simp [lift, lam, SynTerm.lift]

theorem lift_var {k i} : lift k (var i) = var (if i >= k then Nat.succ i else i) := by
  simp [lift, var, SynTerm.lift]

theorem lift_const {k c} : lift k (const c) = const c := by
  simp [lift, const, SynTerm.lift]

theorem subst_app {i t t1 t2}
  : subst i t (app t1 t2) = app (subst i t t1) (subst i t t2) := by
  apply Quotient.ind _ t
  apply Quotient.ind _ t1
  apply Quotient.ind _ t2
  intros
  simp [subst, app, SynTerm.subst]

theorem subst_lam {i s t t1} : subst i t (lam s t1) = lam s (subst (Nat.succ i) (lift 0 t) t1) := by
  apply Quotient.ind _ t
  apply Quotient.ind _ t1
  intros
  simp [subst, lift, lam, SynTerm.subst]

theorem subst_var {k i t} : subst k t (var i)
  = if k < i then var (Nat.pred i) else if i == k then t else var i := by
  apply Quotient.ind _ t
  intros
  simp [subst, var, SynTerm.subst]
  repeat' (first | split | trivial)

theorem liftLiftMulti (n i : Nat) (H : i ≤ n) (t : QTerm)
  : lift i (liftMulti n t) = liftMulti (Nat.succ n) t := by
  apply Quotient.ind _ t
  intros
  simp [lift, liftMulti]
  apply Quotient.sound
  rw [SynTerm.liftLiftMulti n i H]
  simp
  apply refl

theorem substLiftMulti (n i : Nat) (t1 t2 : QTerm) (H : i < n)
  : subst i t1 (liftMulti n t2) = liftMulti (Nat.pred n) t2 := by
  apply Quotient.ind _ t1
  apply Quotient.ind _ t2
  intros t1 t2
  simp [subst, liftMulti]
  apply Quotient.sound
  rw [SynTerm.substLiftMulti n i t2 t1 H]
  simp
  apply refl

theorem subst_const {k t c} : subst k t (const c) = const c := by
  apply Quotient.ind _ t
  simp [subst, const, SynTerm.subst]

theorem liftMultiZero (t : QTerm) : liftMulti 0 t = t := by
  apply Quotient.ind _ t
  intros
  simp [liftMulti]
  rfl

theorem beta {s} {N M : QTerm} : app (lam s N) M = subst 0 M N := by
  apply Quotient.ind _ N
  apply Quotient.ind _ M
  intros N M
  simp [subst, app, lam]
  apply Quotient.sound
  refine ⟨SynTerm.subst 0 N M, ⟨?_, ?_⟩⟩
  · apply oneStep
    apply union.r
    apply Step.beta
  · apply closure.refl

theorem eta {s} {M : QTerm} : lam s (app (lift 0 M) (var 0)) = M := by
  apply Quotient.ind _ M
  intros M
  simp [lam, lift, var, app, lam]
  apply Quotient.sound
  refine ⟨M, ⟨?_, ?_⟩⟩
  · apply oneStep
    apply union.s
    apply StepEta.eta
    rfl
  · apply closure.refl

theorem alpha {s1 s2} {t : QTerm} : lam s1 t = lam s2 t := by
  apply Quotient.ind _ t
  intros t
  simp [lam]
  apply Quotient.sound
  refine ⟨Term.lam s1 t, ⟨?_, ?_⟩⟩
  · apply closure.refl
  · apply oneStep
    apply union.s
    apply StepEta.alpha

theorem const_inj {c1 c2} (H : const c1 = const c2) : c1 = c2 := by
  simp [const] at H
  have H := Quotient.exact H
  rcases H with ⟨t, l, r⟩
  have l := constStep l
  have r := constStep r
  subst_vars
  simp at r
  assumption

theorem var_inj {i1 i2} (H : var i1 = var i2) : i1 = i2 := by
  simp [var] at H
  have H := Quotient.exact H
  rcases H with ⟨t, l, r⟩
  have l := varStep l
  have r := varStep r
  subst_vars
  simp at r
  assumption

theorem var_not_const {i c} (H : var i = const c) : False := by
  simp [var, const] at H
  have H := Quotient.exact H
  rcases H with ⟨t, l, r⟩
  have l := varStep l
  have r := constStep r
  subst_vars
  simp at r

theorem lam_body {t1 t2 s1 s2} (H : lam s1 t1 = lam s2 t2) : t1 = t2 := by
  have H := congrArg (lift 0) H
  have H := congrArg (fun t => app t (var 0)) H
  simp at H
  simp [lift_lam, beta] at H
  revert H
  apply Quotient.ind _ t1
  apply Quotient.ind _ t2
  intros t1 t2 H
  simp [subst, lift, var] at H
  repeat rw [<- SynTerm.subst_lift_2] at H
  assumption

-- TODO: i could put strings on the vars, which don't do anything and there would be an
-- equivalence rule for changing them around.
-- unlike alpha equivalence, it wouldn't be needed for confluence of other stuff maybe?

-----------------------------------------------------------------------------
---- fancy syntax -----------------------------------------------------------
-----------------------------------------------------------------------------

declare_syntax_cat lambda_scope
syntax ident : lambda_scope

-- this really does have to be a big number or some syntax doesn't work
syntax:1500 (name := lambda_scoper) "<" lambda_scope:10 ">" : term
syntax " (" lambda_scope ") " : lambda_scope
syntax " {" term:10 "} " : lambda_scope -- TODO: big-weaken thing!
syntax:60 lambda_scope:60 lambda_scope:61 : lambda_scope
syntax "λ " ident+ ". " lambda_scope : lambda_scope

def firstLetterCapital (s : String) : Bool :=
  Char.isUpper (String.front s)

partial def elabTermImplS (e : Syntax) (varnames: List String) : MetaM (TSyntax `term) :=
  match e with
  | `(< $a:lambda_scope $b:lambda_scope >) => do
    let aarg <- `(< $a >)
    let barg <- `(< $b >)
    let ae : TSyntax `term <- elabTermImplS aarg varnames
    let be <- elabTermImplS barg varnames
    `(app $ae $be)
  | `(< $s:ident >) =>
    let str := toString s.getId
    let strlit : TSyntax `term := Lean.quote (str)
    if firstLetterCapital str
      then `(const (Constant.strConst $strlit))
      else do
        -- TODO: here is where i should program in an error message if its out of bounds,
        -- idxOf just silently returns a value if its not in the list
        -- let i := Lean.quote (varnames.length - varnames.idxOf str - 1)
        let i := Lean.quote (varnames.idxOf str)
        `(var $i)
  | `(< λ $xs:ident* . $body:lambda_scope >) => do
    let mut varnames := varnames
    for x in xs do
      varnames := (toString x.getId) :: varnames
    let bodyarg <- `(< $body >)
    let mut acc <- elabTermImplS bodyarg varnames
    for x in xs.reverse do
      acc <- `(lam $(Lean.quote (toString x.getId)) $acc)
    return acc
  | `(< ( $t:lambda_scope ) >) => do
    let ts <- `(< $t >)
    elabTermImplS ts varnames
  | `(< {$t:term} >) =>
    let n := Lean.quote (varnames.length)
    `(liftMulti $n $t)
  | _ => throwError "other"

@[term_elab lambda_scoper]
def elabTerm : TermElab := fun stx _typ? => do
  let `(< $_t >) := stx | throwError "error"
  -- elabTermImpl stx ctx []
  let res <- (elabTermImplS stx [])
  Term.elabTerm res (Option.some q(QTerm))

def test_term := <λ x. A x x>

#check (<λ x. A>) = (<λ x y z. (x y z q r s)>)
#check (<λ x y. {test_term}>) = (<λ x y z. (x y)>)
#check < λ x y . A B >
#check < λ x y . x y >
-- #check <λ n. λ s z. s (n s z)>
#check <λ x. λ y. x y>
#check <A B>

partial def ppTermImpl (t : Expr) (varnames : List String) : Delab := do
  match t with
  | Expr.app (Expr.app (Expr.const `QuotTerm.lam _) s) t =>
    let s' : Expr := s
    let (Expr.lit (Literal.strVal str)) := s' | failure
    let `(< $s >) <- ppTermImpl t (str :: varnames) | failure
    let name : Syntax := mkIdent <| Name.mkSimple str
    let tname : TSyntax _ := {raw := name}
    `(< λ $tname . $s>)
  | Expr.app (Expr.const `QuotTerm.const _)
    (Expr.app (Expr.const `SynTerm.Constant.strConst _) s) =>
    let s' : Expr := s
    let (Expr.lit (Literal.strVal str)) := s' | failure
    let name : Syntax := mkIdent <| Name.mkSimple str
    let tname : TSyntax _ := {raw := name}
    `(< $tname >)
  | Expr.app (Expr.const `QuotTerm.var _) v =>
    -- let i <- natExprToNat v
    if match v with
       | Expr.app (Expr.app (Expr.app (Expr.const `OfNat.ofNat _) _) _) _  => false
       | _ => true
    then failure
    else
    let i <- unsafe evalExpr Nat (.const `Nat []) v
    match varnames[i]? with
    | Option.some str =>
      let name : Syntax := mkIdent <| Name.mkSimple str
      let tname : TSyntax _ := {raw := name}
      `(< $tname >)
    | Option.none =>
      let str := "freevar".append i.toSubscriptString
      let name : Syntax := mkIdent <| Name.mkSimple str
      let tname : TSyntax _ := {raw := name}
      `(< $tname >)
  | Expr.app (Expr.app (Expr.const `QuotTerm.app _) t1) t2 =>
    let `(< $s1 >) <- ppTermImpl t1 varnames | failure
    let `(< $s2 >) <- ppTermImpl t2 varnames | failure
    let parena := match t1 with
      | Expr.app (Expr.app (Expr.const `QuotTerm.lam _) _) _ => true
      | _ => false
    let parenb := match t2 with
      | Expr.app (Expr.app (Expr.const `QuotTerm.lam _) _) _ => true
      | Expr.app (Expr.app (Expr.const `QuotTerm.app _) _) _ => true
      | _ => false
    -- `(< $s1 $s2 >)
    match parena, parenb with
    | false, false => `(< $s1 $s2 >)
    | false, true => `(< $s1 ($s2) >)
    | true, false => `(< ($s1) $s2 >)
    | true, true => `(< ($s1) ($s2) >)
  | Expr.app (Expr.app (Expr.const `QuotTerm.liftMulti _) _n) t =>
    let ts <- delab t
    `(< { $ts } >)
  | _ => failure

-- we can only trigger delaborators for top level things. so we need one for each constructor
@[delab app.QuotTerm.app]
def delabApp : Delab := do
  let e <- getExpr
  ppTermImpl e []
@[delab app.QuotTerm.lam]
def delabLam : Delab := do
  let e <- getExpr
  ppTermImpl e []
@[delab app.QuotTerm.const]
def delabConst : Delab := do
  let e <- getExpr
  ppTermImpl e []
@[delab app.QuotTerm.var]
def delabVar : Delab := do
  let e <- getExpr
  ppTermImpl e []

#check OfNat.ofNat
-- set_option pp.rawOnError true
#check <λ x y. {test_term}>
#check <λ x. A> = <λ x y z. (x y)>
#check <A B>
#check <A>
#check <(A B) (C (λ x. x))>
#check <λ x . A>
#check <λ x . x>
#check <λ x y . x y>
#check <(A)(B)>
#check <(A B)(B)>
def something := <λ x y. { _ }>

end QuotTerm

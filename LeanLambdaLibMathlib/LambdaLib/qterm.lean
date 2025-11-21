import LambdaLib.term

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

def lam (s : String) (t : QTerm) : QTerm :=
  Quotient.map (Term.lam s) (respectStepLemma (Term.lam s) Step.lam StepEta.lam) t

def app (t1 t2 : QTerm) : QTerm :=
  Quotient.map₂ Term.app
    (respectStepLemma2 Term.app (oneStep ∘ Step.app1) (oneStep ∘ StepEta.app1)
      (oneStep ∘ Step.app2) (oneStep ∘ StepEta.app2)) t1 t2

def var (i : Nat) : QTerm := Quotient.mk _ (Term.var i)

-- TODO: namespaces
def lift2 (i : Nat) (t : QTerm) : QTerm :=
  Quotient.map (lift i) (respectStepLemma (lift i) liftStep etaLift) t

def subst2 (i : Nat) (t1 t2 : QTerm) : QTerm :=
  Quotient.map₂ (subst i)
    (respectStepLemma2 (subst i) substStep1 etaSubst1
      (oneStep ∘ substStep2 _ _) (oneStep ∘ etaSubst2 _ _)) t1 t2

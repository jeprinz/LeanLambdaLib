-- from prog2.v in my rocq version
import Mathlib.Logic.Basic

-- TODO: if i do the (A → Prop) version, then i don't need Type 2.
-- TODO: can i disable universe level checking to see if different universes are
-- causing the conv bug in test.lean?
inductive Prog (A B : Type) : Type 2 where
| Ret : Option B → Prog A B
| Rec : ∀ (I : Type), (I → A) → ((I → B) → Prog A B) → Prog A B

inductive runProgR {A B : Type} (prog : A → Prog A B) : Prog A B → B → Prop where
| retR : ∀ (b), runProgR prog (.Ret (Option.some b)) b
| recR : ∀ I (args : I → A) (recVals : I → B) (res : B)
  (rest : (I → B) → Prog A B),
  -- if for all inputs of the form (args i), recVals describes the recursive calls
  (∀ (i : I), runProgR prog (prog (args i)) (recVals i))
  -- and given the results of those recursive calls, the program outputs `res'
  → runProgR prog (rest recVals) res
  -- then overall the results is `res'
  → runProgR prog (.Rec I args rest) res

theorem runProgFunction {A B : Type} {prog : A → Prog A B} {p : Prog A B} {b1 b2 : B}
  (rp1 : runProgR prog p b1) (rp2 : runProgR prog p b2) : b1 = b2 := by
  induction rp1 generalizing b2 with
  | retR =>
    cases rp2
    rfl
  | recR I1 args1 recVals1 res1 rest1 recCall1 finalCall1 ihRec ihFinal =>
    cases rp2 with | recR I2 args2 recVals2 res2 rest2 recCall2 finalCall2 =>
    have recFact : recVals1 = recVals2 := by
      apply funext
      intros i
      apply ihRec i (recCall2 i)
    subst recVals1
    apply ihFinal
    apply finalCall2

#check Classical.choose

noncomputable def chooseOption (T : Type) (P : T → Prop) : Option T :=
  @Classical.choose (Option T)
    (fun ot => match ot with
               | .some t => P t
               | .none => ¬ ∃ t, P t)
    (by
      cases (Classical.em (exists t, P t)) with
      | inl p =>
        rcases p with ⟨x, Pt⟩
        exists x
      | inr p =>
        exists .none
    )

#check Classical.some_spec₂

theorem chooseOptionSpec1 (T P t) : chooseOption T P = .some t → P t := by
    unfold chooseOption
    apply Classical.some_spec₂ (fun q => q = some t → P t)
    intros a fact eq
    subst a
    cases some t <;> grind

theorem chooseOptionSpec2 (T P) : chooseOption T P = .none → ¬ ∃ t, P t := by
  unfold chooseOption
  apply Classical.some_spec₂ (fun q => q = none → ¬ ∃ t, P t)
  intros ot fact eq
  subst ot
  simp at *
  assumption

noncomputable def runProgImpl {A B : Type} (prog : A → Prog A B) (p : Prog A B) : Option B :=
  chooseOption B (fun b => runProgR prog p b)

noncomputable def runProg {A B : Type} (prog : A → Prog A B) (a : A) : Option B :=
  runProgImpl prog (prog a)

theorem runProgDefinitionRet {A B : Type} (prog : A → Prog A B) (b : Option B)
  : runProgImpl prog (.Ret b) = b := by
    unfold runProgImpl chooseOption
    apply Classical.some_spec₂ (fun q => q = b)
    intros a fact
    simp at *
    cases a with
    | some a =>
      simp at fact
      cases fact
      rfl
    | none =>
      simp at fact
      cases b with
      | some b =>
        exfalso
        apply fact b
        constructor
      | none => rfl

noncomputable def collectOption {A B : Type} (f : A → Option B) : Option (A → B) :=
  (chooseOption (A → B) (fun f' => ∀ a, .some (f' a) = f a))


theorem collectOptionDef {A B : Type} (f : A → B)
  : collectOption (fun a => some (f a)) = some f := by
  unfold collectOption chooseOption
  apply Classical.some_spec₂ (fun q => q = some f)
  intros f fact
  simp at *
  cases f with
  | none =>
    simp at *
    have fact := fact f
    simp at fact
  | some f =>
    simp at *
    apply funext
    assumption

theorem runProgDefinitionRec {A B : Type} {prog : A → Prog A B}
  {I : Type}
  {args : I → A}
  {rest : (I → B) → Prog A B}
  : runProgImpl prog (.Rec I args rest) =
    Option.bind (collectOption (fun i => runProg prog (args i)))
      (fun f => runProgImpl prog (rest f))
  := by
  unfold runProgImpl chooseOption
  -- have to do the 'thing shuffle' for stupid reasons
  generalize h1 : ((collectOption fun i ↦ runProg prog (args i)).bind fun f ↦
    Classical.choose _) = thing
  apply Classical.some_spec₂ (fun q => q = thing)
  subst thing
  intros a fact
  simp at *
  cases a with
  | none =>
    simp at *
    unfold collectOption chooseOption
    generalize h1 : (fun f ↦ Classical.choose _) = thing
    apply Classical.some_spec₂ (fun q => none = Option.bind q thing)
    subst thing
    intros recVals p
    simp at *
    cases recVals with
    | none =>
      simp at *
    | some x =>
      simp at *
      apply Classical.some_spec₂
      intros ob q
      cases ob with
      | none => grind
      | some b =>
        simp at *
        apply fact
        refine (runProgR.recR _ _ x b _ ?_ q)
        intros i
        have p := p i
        unfold runProg runProgImpl at p
        symm at p
        have p := chooseOptionSpec1 _ _ _ p
        assumption
  | some a =>
    simp at *
    cases fact with
    | recR b _ recVals _ _ recCalls finalCall => _
    have H : ∀ i, runProg prog (args i) = some (recVals i) := by
      intros i
      unfold runProg runProgImpl chooseOption
      apply Classical.some_spec₂ (fun q => q = some (recVals i))
      simp
      intros ob fact
      cases ob <;> grind [runProgFunction]
    conv =>
      rhs
      congr
      · congr
        · ext
          rw [H]
    rw [collectOptionDef]
    simp
    apply Classical.some_spec₂
    intros ob fact
    cases ob <;> grind [runProgFunction]



-- now, to test it out on a difficult case:
-- from test_function_5 in rocq version

import LambdaLib.qterm
import LambdaLib.unification
import LambdaLib.functions.pmatch
import LambdaLib.functions.prog
-- import Mathlib.Tactic

-- this file has test cases that i need to work for the embedding
-- to eventually work

open QuotTerm

namespace S
abbrev pair := <λ t1 t2 p. p t1 t2>
abbrev proj1 := <λ p. p (λ x y. x)>
abbrev proj2 := <λ p. p (λ x y. y)>
-- TODO: i can make syntax for pair with a macro, which will run before the elaborator!

-- contexts
abbrev nil := <Nil>
abbrev cons := <λ ctx lvl ty. Cons ctx lvl ty>

-- variables
abbrev zero := <λ env. {proj2} env>
abbrev succ := <λ x env. x ({proj1} env)>

abbrev pi := <λ x y env. Pi (x env) (λ a. y ({pair} env a))>
abbrev U := <λ env. U>
abbrev Empty := <λ env. Empty>
abbrev Lift := <λ T env. Lift (T env)>
end S

noncomputable def means_prog (prev : QTerm → Option (QTerm → Prop))
  (ty : QTerm) : Prog QTerm (QTerm → Prop) :=
  Pmatch2
    (fun A B ↦ ty = <Pi {A} {B}>)
    (fun A B => .Rec PUnit (fun _ => A)
      (fun mA => .Rec {a // mA .unit a} (fun ⟨a, _aInA⟩ ↦ <{B} {a}>)
      (fun mBa ↦ .Ret (some
        (fun f ↦ ∀ (a : QTerm) (inA : mA .unit a), mBa ⟨a, inA⟩ <{f} {a}>)))))
  (Pif (ty = <U>)
    (.Ret (some (fun T ↦ ∃ S, prev T = some S)))
    -- (.Ret (recorder prev))
    -- catchall case shouldn't happen
    (.Ret .none))

noncomputable def means'
  (prev : QTerm → Option (QTerm → Prop))
  (ty : QTerm)
  : Option (QTerm → Prop)
  := runProg (means_prog prev) ty

noncomputable def means (lvl : Nat) (ty : QTerm) : Option (QTerm → Prop) :=
  match lvl with
  | .zero => none -- some (fun _ ↦ False)
  -- | .succ lvl' => means' (means lvl') ty
  | .succ lvl' => runProg (means_prog (means lvl')) ty

example (SA SB A B)
  (rec1 : means 1 A = some SA)
  (rec2 : means 1 B = some SB)
  : means 1 <Pi {A} (λ a. {B})> = some (fun f ↦ ∀ a, SA a → SB <{f} {a}>)
  := by
  --
  repeat (first
    | simp only [means, means', means_prog]
    | simp only [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
    | simp (disch := intros; lambda_solve; try trivial) only [PmatchDef1, PmatchDef2]
    | simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1, Pmatch2Def2]
    | simp (disch := intros; lambda_solve; try trivial) only [PifDef1, PifDef2]
  )
  --
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at rec1
  --
  -- rewrite [rec1]
  rewrite [rec1]
  --
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at rec2
  normalize
  --
  rewrite [rec2]
  clear rec1 rec2
  simp only [collectOptionDef, mybindDef1]
  --

macro "normalize2" : tactic => `(tactic|
  simp only [lift_app, lift_lam, lift_var, lift_const,
      subst_app, subst_lam, subst_var, subst_const,
      liftLiftMulti, substLiftMulti, liftMultiZero,
      liftMulti_lam_rw, liftMulti_app_rw, liftMulti_var_rw, liftMulti_const_rw,
      beta] at *
)

macro "lambda_solve2" : tactic => `(tactic|
  repeat ( first
    | trivial
    -- | simp at * -- TODO: figure out which lemmas this is using (relating to ∧) and write explicitly
    -- | normalize2
    -- | simp only [lam_body_rw, const_inj_rw, var_inj_rw, var_not_const_rw, var_not_const_rw2] at *
    -- | simp (disch := repeat constructor) only [app_fact_rw, app_ne_const_rw, app_ne_var_rw] at *
    | fail_if_no_progress subst_vars -- TODO: maybe only have this go on equations of type QTerm
    | casesm* _ ∧ _, QTerm × QTerm
    | simp [*] -- TODO: maybe i can use the `contextual' flag instead
  )
)

-- this one was giving more trouble in embedding.lean
example {mty env} {lvl : Nat}
  (H : means lvl.succ.succ (< {S.U} {env} >) = some mty)
  : False
  := by
  --
  -- the clear H makes it run fast instead of slow
  repeat (first
    | simp only [means, means', means_prog, runProg, runProgDefinitionRet,
      runProgDefinitionRec, collectOptionDef] at H
    | simp (disch := clear H; intros; lambda_solve; try trivial) only
      [PmatchDef1, PmatchDef2, Pmatch2Def1, Pmatch2Def2, PifDef1, PifDef2] at H
  )
  --
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at H
  --
  -- lambda_solve
  --
  simp (disch := clear H; intros; lambda_solve; try trivial) only
    [PmatchDef1, PmatchDef2, Pmatch2Def1, Pmatch2Def2, PifDef1, PifDef2] at H
  --
  simp (disch := intros; lambda_solve; try trivial) only [PifDef1, PifDef2] at H
  -- this is now slow again.......
  simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1, Pmatch2Def2] at H
  --
  sorry

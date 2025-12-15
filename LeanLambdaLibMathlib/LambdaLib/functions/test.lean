import LambdaLib.functions.pmatch
import LambdaLib.functions.prog
import LambdaLib.qterm
import LambdaLib.unification
-- import Mathlib.Tactic.failIfNoProgress

open QuotTerm

noncomputable def match_test_function (t : QTerm) : QTerm := Pmatch
    (fun x ↦ t = <A {x} >)
    (fun x => <Matched {x} >)
    <Didnt Match>

theorem match_test : match_test_function <A B> = <Matched B> := by
  unfold match_test_function
  simp (disch := (intros ; lambda_solve; try trivial)) [PmatchDef1]
  lambda_solve

theorem match_test_2 : match_test_function <C B> = <Didnt Match> := by
  unfold match_test_function
  simp (disch := (intros ; lambda_solve; try trivial)) [PmatchDef2]

noncomputable def match2_test_function (t : QTerm) : QTerm := Pmatch2
    (fun x y ↦ t = <A {x} {y} >)
    (fun x y => <Matched {x} {y} >)
    <Didnt Match>

theorem match2_test : match2_test_function <A B C> = <Matched B C> := by
  unfold match2_test_function
  simp (disch := (intros ; lambda_solve; try trivial)) [Pmatch2Def1]
  lambda_solve

theorem match2_test_2 : match2_test_function <C B> = <Didnt Match> := by
  unfold match2_test_function
  simp (disch := (intros ; lambda_solve; try trivial)) [Pmatch2Def2]

-- noncomputable def match_test_function3 (t : QTerm) : QTerm := Pmatch
--     (fun (Prod.mk x y) ↦ t = <A {x} {y} >)
--     (fun (Prod.mk x y) => <Matched {x} {y} >)
--     <Didnt Match>

-- set_option trace.Meta.Tactic.simp.discharge true
-- theorem match_test3 : match_test_function3 <A B> = <Matched B> := by
--   unfold match_test_function3
--   simp (disch := (intros ; casesm* QTerm × QTerm;  lambda_solve; try trivial)) [PmatchDef1]
--   lambda_solve

-- theorem match_test_32 : match_test_function3 <C B> = <Didnt Match> := by
--   unfold match_test_function3
--   simp (disch := (intros ; lambda_solve; try trivial)) [PmatchDef2]

noncomputable def test_function_part (t : QTerm) : Prog QTerm QTerm :=
  Pmatch
    (fun x ↦ t = <A {x}>)
    (fun x => .Rec PUnit
      (fun u => match u with | _tt => x)
      (fun res => .Ret (some <B {res .unit}>)))
    (.Ret <D>)
    -- NOTE: in the above line, the Option.some is automatically inserted
    -- i should learn about how lean does this

noncomputable def test_function : QTerm → Option QTerm := runProg test_function_part

theorem run_test_function : test_function <A C> = some <B D> := by
  simp [test_function]
  repeat (first
    | simp [test_function_part]
    | simp [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
    -- turns out that simp can go under binders even though rw can't!
    | simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2]
  )
  lambda_solve

theorem run_test_function_2 : test_function <A (A (A (A C)))> = some <B (B (B (B D)))> := by
  simp [test_function]

  -- trying to put it all in one big tactic
  repeat (first
    | simp [test_function_part]
    | simp [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
    | simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2]
  )
  --
  lambda_solve
  --

-- TODO:
-- 1) state fundamental lemma
-- 2) possibly think of a minimal example that is closer to the fundamental lemma
--    to test on.

namespace S
abbrev pair := <λ t1 t2 p. p t1 t2>
abbrev pi := <λ x y env. Pi (x env) (λ a. y ({pair} env a))>
abbrev U := <λ env. U>
end S

example : <{S.pi} A B> = <A> := by
  unfold S.pi
  normalize
  --
  sorry

-- TODO: here it is!
example (env A B : QTerm)
  (H : < {S.U} {env} > = <Pi {A} {B} >)
  : False := by
  lambda_solve
  --


-- the match problem from embedding.lean
example (env : QTerm)
  : Pmatch2
    (fun A B ↦ <{S.U} {env}> = <Pi {A} {B}>)
    (fun _ _ ↦ true)
    false
    = false := by
  --
  unfold S.U
  normalize
  --
  simp (disch := intros; lambda_solve; try trivial) [Pmatch2Def2]

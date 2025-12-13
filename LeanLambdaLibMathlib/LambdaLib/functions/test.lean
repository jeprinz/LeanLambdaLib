import LambdaLib.functions.pmatch
import LambdaLib.functions.prog
import LambdaLib.qterm
import LambdaLib.unification

open QuotTerm

noncomputable def match_test_function (t : QTerm) : QTerm := Pmatch
    (fun x ↦ t = <A {x}>)
    (fun x => <Matched {x}>)
    <Didnt Match>

theorem match_test : match_test_function <A B> = <Matched B> := by
  unfold match_test_function
  -- i want the following to work:
  simp (disch := (intros ; lambda_solve; try trivial)) [PmatchDef1]
  lambda_solve
  --
  -- rw [PmatchDef1] <;> try (intros; lambda_solve; try trivial)
  --

theorem match_test_2 : match_test_function <C B> = <Didnt Match> := by
  unfold match_test_function
  -- rw [PmatchDef2]
  -- intros
  -- lambda_solve
  simp (disch := (intros ; lambda_solve; try trivial)) [PmatchDef2]

noncomputable def test_function_part (t : QTerm) : Prog QTerm QTerm :=
  Pmatch
    (fun x ↦ t = <A {x}>)
    (fun x => .Rec PUnit
      (fun u => match u with | _tt => x)
      (fun res => .Ret (some <B {res .unit}>)))
    (.Ret <D>)

noncomputable def test_function : QTerm → Option QTerm := runProg test_function_part

axiom test.{u} {T : Type u} : T
axiom test_rw.{u1, u2} {T : Type u1} {A : Type u2} (P : T → Prop)
  (branch1 : T → A) (branch2 : A) : Pmatch P branch1 branch2 = test
axiom test_rw_2.{u} {T : Type u} {t : T} : t = test

theorem run_test_function : test_function <A C> = some <B D> := by
  unfold test_function
  unfold runProg
  --
  -- unfold test_function_part at 2
  conv in (occs := 2) (test_function_part) => unfold test_function_part
  simp
  --
  --
  --
  --
  -- this should in principle evaluate any matches that can be evaluated
  conv in (occs := *) (Pmatch _ _ _) => all_goals
    simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2]
  --
  simp [runProgDefinitionRec, runProgDefinitionRet]
  unfold runProg
  simp [test_function_part]
  --
  --
  -- conv in (occs := *) (Pmatch _ _ _) => all_goals
    -- simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2]
  --
  -- here, the above 'should in principle' tactic doesn't work, so we need
  -- to go under the l.h.s of the bind first. i think its a lean bug.
  conv => {
    conv in (occs := *) (Option.bind _ _) => all_goals
    congr
    · conv in (occs := *) (Pmatch _ _ _) => all_goals
      simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2]
  }
  --
  --
  simp [runProgDefinitionRet]
  simp [collectOptionDef]
  lambda_solve


-- is there a way to get it to try something for every matching pattern in conv?
-- https://leanprover-community.github.io/extras/conv.html

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

theorem run_test_function : test_function <A C> = some <B D> := by
  unfold test_function test_function_part
  unfold runProg
  simp
  --
  -- conv in (occs := *) (Pmatch _ _ _) =>
  --   all_goals simp (disch := lambda_solve) [test_rw]
  --
  conv in (occs := *) (Pmatch _ _ _) => all_goals
    simp (disch := intros; lambda_solve; try trivial) [PmatchDef1]
  --
  simp [runProgDefinitionRec, runProgDefinitionRet]
  --
  sorry


-- is there a way to get it to try something for every matching pattern in conv?
-- https://leanprover-community.github.io/extras/conv.html

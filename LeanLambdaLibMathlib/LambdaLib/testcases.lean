import LambdaLib.qterm
import LambdaLib.unification
import LambdaLib.functions.pmatch
import LambdaLib.functions.prog

-- this file has test cases that i need to work for the embedding
-- to eventually work

open QuotTerm

-- in this file, i'll define dependent type theory and prove canonicity

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
  | .succ lvl' => means' (means lvl') ty

inductive means_ctx : QTerm → QTerm → Prop where
| in_nil : means_ctx S.nil S.nil
| in_cons : ∀ {env ctx lvl val T s},
  means_ctx env ctx
  → means (.succ lvl) <{T} {env}> = some s
  → s val
  → means_ctx <{S.pair} {env} {val}> <{S.cons} {ctx} {const (.natConst lvl)} {T}>

-- TODO: get this sort of things to work!
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
  sorry

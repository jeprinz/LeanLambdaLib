import LambdaLib.qterm
import LambdaLib.unification
import LambdaLib.functions.pmatch
import LambdaLib.functions.prog

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

abbrev lambda := <λ t env a. t ({pair} env a)>
abbrev app := <λ t1 t2 env. (t1 env) (t2 env)>

abbrev weaken := <λ t env. t ({proj1} env)>
abbrev subLast := <λ t toSub env. t ({pair} env (toSub env))>
end S

inductive VarTyped : QTerm → Nat → QTerm → QTerm → Prop where
| zero : ∀{ctx T lvl},
  VarTyped <{S.cons} {ctx} {const (.natConst lvl)} {T}> lvl <{S.weaken} {T}> zero
| succ : ∀{ctx A T s lvl1 lvl2}, VarTyped ctx lvl1 A s
  → VarTyped <{S.cons} {ctx} {lvl2} {T}> lvl1 <{S.weaken} {A}> <{succ} {s}>

-- context → level → type → term → prop
inductive Typed : QTerm → Nat → QTerm → QTerm → Prop where
| lambda : ∀{ctx A B s lvl}, Typed ctx (Nat.succ lvl) S.U <{S.pi} {A} {B}>
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl B s
  → Typed ctx lvl <{S.pi} {A} {B}> <{S.lambda} {s}>
| app : ∀{ctx A B s1 s2 lvl}, Typed ctx lvl <{S.pi} {A} {B}> s1 → Typed ctx lvl A s2
  → Typed ctx lvl <{S.subLast} {B} {s2}> <{S.app} {s1} {s2}>
| var : ∀{ctx T t lvl}, VarTyped ctx lvl T t → Typed ctx lvl T t
| Empty : ∀{ctx}, Typed ctx 1 S.U S.Empty
| U : ∀{ctx lvl}, Typed ctx (2 + lvl) S.U S.U
| Lift : ∀{ctx lvl T}, Typed ctx (1 + lvl) S.U T → Typed ctx (2 + lvl) S.U <{S.Lift} {T}>
| lift : ∀{ctx lvl T t}, Typed ctx lvl T t → Typed ctx (1 + lvl) <{S.Lift} {T}> t
| lower : ∀{ctx lvl T t}, Typed ctx (1 + lvl) <{S.Lift} {T}> t → Typed ctx lvl T t

axiom recorder : {T Out : Type} → T → Out

-- next goal should be to build syntax or whatever is needed so that
-- this definition can be as readable as possible.
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

-- noncomputable def means_ctx : QTerm → Option (QTerm → Prop) :=
--   runProg fun ctx ↦
--     Pmatch3
--     (fun ctx' lvl ty ↦ ctx = <{S.cons} {ctx'} {lvl} {ty}>)
--     (fun ctx' lvl ty ↦ .Rec PUnit (fun _ ↦ ctx')
--       (fun mctx' ↦ .Ret (some (_))))
--     -- nil case
--     (.Ret (some (fun q ↦ q = S.nil)))

inductive means_ctx : QTerm → QTerm → Prop where
| in_nil : means_ctx S.nil S.nil
| in_cons : ∀ {env ctx lvl val T s},
  means_ctx env ctx
  → means (.succ lvl) <{T} {env}> = some s
  → s val
  → means_ctx <{S.pair} {env} {val}> <{S.cons} {ctx} {const (.natConst lvl)} {T}>

example (bla) : means 1 <U> = bla := by
  --
  repeat (first
    | simp only [means, means', means_prog]
    | simp only [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
    | simp (disch := intros; lambda_solve; try trivial) only [PmatchDef1, PmatchDef2]
    | simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1, Pmatch2Def2]
    | simp (disch := intros; lambda_solve; try trivial) only [PifDef1, PifDef2]
  )
  sorry

-- means 0 <U> is the empty set, so means <Pi U (λ a. U)> is all terms, since all terms
-- given any element of the empty set produce an element of the empty set.
example (bla) : means 1 <Pi U (λ a. U)> = bla := by
  --
  -- simp [means, means', means_prog]
  -- simp [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
  -- simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2]
  -- simp (disch := intros; lambda_solve; try trivial) [Pmatch2Def1, Pmatch2Def2]
  -- simp (disch := intros; lambda_solve; try trivial) [PifDef1, PifDef2]
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
  simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1, Pmatch2Def2]
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
  simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1, Pmatch2Def2]
  simp (disch := intros; lambda_solve; try trivial) only [PifDef1, PifDef2]
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
  simp only [Option.bind]
  simp
  --
  simp (disch := intros; lambda_solve; try trivial) only [PifDef1, PifDef2]
  --
  sorry

-- TODO: get this sort of things to work!
example (SA SB A B)
  (rec1 : means 1 A = some SA)
  (rec2 : means 1 B = some SB)
  : means 1 <Pi {A} (λ a. {B})> = some (fun f ↦ ∀ a, SA a → SB <{f} {a}>)
  := by
  --
  sorry

example (H : means 1 <U> = .none) : False := by
  --
  repeat (first
    | simp [means, means', means_prog] at H
    | simp [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at H
    | simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2] at H
    | simp (disch := intros; lambda_solve; try trivial) [Pmatch2Def1, Pmatch2Def2] at H
    | simp (disch := intros; lambda_solve; try trivial) [PifDef1, PifDef2] at H
  )
  -- TODO: why does the above compute if its in the goal but not if its in the ctx?
  sorry

-- set_option diagnostics true
theorem fundamental_lemma {ctx T lvl t env}
  (mT : Typed ctx lvl T t)
  (mctx : means_ctx env ctx)
  : ∃ s, means (.succ lvl) <{T} {env}> = some s ∧ s <{t} {env}>
  :=
  match mT with
  | .lambda ty body => by
    have ⟨mty, mtyeq, bla⟩ := fundamental_lemma ty mctx
    --
    -- unfold means at mtyeq
    -- repeat (first
    --   | simp [means, means', means_prog] at mtyeq
    --   | simp [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at mtyeq
    --   | simp (disch := intros; lambda_solve; try trivial) [PmatchDef1, PmatchDef2] at mtyeq
    --   | simp (disch := intros; lambda_solve; try trivial) [Pmatch2Def1, Pmatch2Def2] at mtyeq
    -- )
    simp [means, means', means_prog, runProg] at mtyeq
    simp (disch := intros; lambda_solve; try trivial) [Pmatch2Def2] at mtyeq
    --
    -- unfold S.U at mtyeq
    --
    --
    --
    have thing := fundamental_lemma body (.in_cons mctx mtyeq bla)
    --
    sorry
  | .app _ _ => sorry
  | .var _ => sorry
  | .Empty => sorry
  | .U => sorry
  | .Lift _ => sorry
  | .lift _ => sorry
  | .lower _ => sorry

/-
[ ] - find classical source for this proof
[ ] - think it through on paper
-/

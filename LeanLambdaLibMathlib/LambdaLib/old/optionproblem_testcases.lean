import LambdaLib.qterm
import LambdaLib.unification
import LambdaLib.functions.pmatch
import LambdaLib.functions.prog

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

inductive means_ctx : QTerm → QTerm → Prop where
| in_nil : means_ctx S.nil S.nil
| in_cons : ∀ {env ctx lvl val T s},
  means_ctx env ctx
  → means (.succ lvl) <{T} {env}> = some s
  → s val
  → means_ctx <{S.pair} {env} {val}> <{S.cons} {ctx} {const (.natConst lvl)} {T}>

macro "simp1" : tactic => `(tactic|
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
)
macro "simp2" : tactic => `(tactic|
  simp (disch := intros; lambda_solve; try trivial) only [PmatchDef1, PmatchDef2,
    Pmatch2Def1, Pmatch2Def2, PifDef1, PifDef2]
)

example (SA A)
  (rec1 : means 1 A = some SA)
  : means 1 A = SA
  := by
  --
  simp1
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at rec1
  rewrite [rec1]
  --
  sorry

def mybind1 : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a

theorem gothere : @Option.bind = @mybind1 := by
  ext X Y a b
  cases a <;> trivial

theorem goback : @mybind1 = @Option.bind := by
  rw [gothere]

-- set_option diagnostics true
-- TODO: get this sort of things to work!
example (SA SB A B)
  (rec1 : means 1 A = some SA)
  (rec2 : means 1 B = some SB)
  : means 1 <Pi {A} (λ a. {B})> = some (fun f ↦ ∀ a, SA a → SB <{f} {a}>)
  := by
  --
  -- repeat (first
  --   | simp only [means, means', means_prog]
  --   | simp only [runProg, runProgDefinitionRet, runProgDefinitionRec, collectOptionDef]
  --   | simp (disch := intros; lambda_solve; try trivial) only [PmatchDef1, PmatchDef2]
  --   | simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1, Pmatch2Def2]
  --   | simp (disch := intros; lambda_solve; try trivial) only [PifDef1, PifDef2]
  -- )
  simp1
  --
  -- simp2
  simp (maxDischargeDepth := 1) (disch := intros; lambda_solve; try trivial)
    only [PmatchDef1, PmatchDef2, Pmatch2Def1, Pmatch2Def2, PifDef1, PifDef2]
  simp1
  -- OK, so if i get rid of the Option.bind's, then it works.
  -- i have no idea what causes the bug though.
  simp only [gothere]
  try simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  simp only [goback]
  -- is it recursively doing simp inside the dispatch?
  --
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at rec1
  --
  rewrite [rec1]
  --
  simp only [means, means', means_prog, runProg,
    runProgDefinitionRet, runProgDefinitionRec, collectOptionDef] at rec2
  normalize
  rewrite [rec2]
  simp [Option.bind, collectOptionDef]
  --
  --

axiom unknown : Prop
axiom hole.{u} {T : Type u} : T

-- trying to isolate the nontermination problem
example
  (A B : QTerm)
  : ((collectOption fun i ↦
          runProgImpl (means_prog fun ty ↦ none)
            (Pmatch2 (fun (A_1 B : QTerm) ↦ A = <Pi {A_1} {B} >)
              (fun _ _ ↦ .Ret none)
              (.Ret none))).bind
      fun a ↦
      (collectOption fun i ↦
            runProgImpl (means_prog fun ty ↦ none)
              (Pmatch2 (fun (A B_1 : QTerm) ↦ B = <Pi {A} {B_1} >)
                (fun _ _ ↦ .Ret none)
                (.Ret none))).bind
        fun a_1 ↦ some fun f ↦ ∀ (a_2 : QTerm) (inA : a PUnit.unit a_2), a_1 a_2 (< {f} {a_2} >)) =
    (none : Option (QTerm → Prop))
  := by
  --
  -- Tactic `simp` failed with a nested error:
  -- (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
  -- simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  --
  sorry

-- can i isolate it more?
example
  (A B : QTerm)
  : ((Pmatch2 (fun (A_1 B : QTerm) ↦ A = <Pi {A_1} {B} >)
              (fun _ _ ↦ none)
              none).bind
      fun (a : Nat) ↦
              (Pmatch2 (fun (A B_1 : QTerm) ↦ B = <Pi {A} {B_1} >)
                (fun _ _ ↦ none)
                none).bind
        fun (a_1 : Nat) ↦ none) =
    (none : Option Nat)
  := by
  --
  -- Tactic `simp` failed with a nested error:
  -- (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
  -- simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  --
  sorry

-- gives a different error but still very slow
example
  (A B : QTerm)
  : ((Pmatch2 (fun (A_1 B : QTerm) ↦ unknown)
              (fun _ _ ↦ none)
              none).bind
      fun (_ : Nat) ↦
              (Pmatch2 (fun (A B_1 : QTerm) ↦ B = <Pi {A} {B_1} >)
                (fun _ _ ↦ none)
                none)) =
    (none : Option Nat)
  := by
  --
  -- just says `simp` made no progress
  -- but takes a while, so still represents a bug i think?
  -- simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  --
  sorry

namespace TestError
@[inline] protected def mybind2 : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a
end TestError

-- in the below, if i replace Option.bind with mybind or mybind2, then
-- the simp fails instantly instead of being very slow
example
  (A B : QTerm)
  : (Option.bind (Pmatch2 (fun (A_1 B : QTerm) ↦ unknown)
              (fun _ _ ↦ none)
              none)
      fun (_ : Nat) ↦
              (Pmatch2 (fun (A B_1 : QTerm) ↦ B = <Pi {A} {B_1} >)
                (fun _ _ ↦ none)
                none)) =
    (none : Option Nat)
  := by
  --
  -- just says `simp` made no progress
  -- but takes a while, so still represents a bug i think?
  -- simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  --
  sorry

-- in this version too,
-- replacing Option.bind with mybind or TestError.mybind2 makes it fail immediately
example
  (A B : QTerm)
  : (Option.bind (Pmatch2 (fun (A_1 B : QTerm) ↦ A = <Pi {A_1} {B} >)
              (fun _ _ ↦ none)
              none)
      fun (a : Nat) ↦
              Option.bind (Pmatch2 (fun (A B_1 : QTerm) ↦ B = <Pi {A} {B_1} >)
                (fun _ _ ↦ none)
                none)
        fun (a_1 : Nat) ↦ none) =
    (none : Option Nat)
  := by
  --
  -- Tactic `simp` failed with a nested error:
  -- (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
  -- simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  --
  sorry

-- so i have no idea what is causing it, but it seems like if i replace
-- Option.bind with my own version of it then it will fix the problem.

-- let's see if i can shrink it more

example
  (A B : QTerm)
  : (Option.bind (Pmatch2 (fun (A_1 B : QTerm) ↦ A = <Pi {A_1} {B} >)
              (fun _ _ ↦ none)
              none)
      fun (a : Nat) ↦
              (Pmatch2 (fun (A B_1 : QTerm) ↦ B = <Pi {A} {B_1} >)
                (fun _ _ ↦ none)
                none)) =
    (none : Option Nat)
  := by
  -- the `simp` made no progress error, but takes a long time to fail.
  -- simp (disch := intros; lambda_solve; try trivial) only [Pmatch2Def1]
  --
  sorry

/-
as far as i can figure out, to trigger the bug, you need
- Option.bind (the one from the standard library, my version doesn't trigger it)
- one of the Pmatch rewrites
- lambda_solve in disch.
-/

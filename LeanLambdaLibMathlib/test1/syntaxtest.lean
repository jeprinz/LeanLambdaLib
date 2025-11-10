/-
notes on lean's syntax mechanisms:
from https://lean-lang.org/doc/reference/latest/Notations-and-Macros/#language-extension
- notations (called operators when infix) are like coq notations, some small differences but basically the same idea.
- the "Defining New Syntax" section describes their syntax tree type, and ways of defining syntax categories
- macros convert syntax to syntax
- elaborators convert syntax to (either commands or terms)


- https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html

- https://stackoverflow.com/questions/79575084/lean4-lambda-calculus-dsl-macro

- https://lean-lang.org/examples/1900-1-1-arithmetic-as-an-embedded-language/

so there are a few things that can work.
[ ] - should i work with scoped or unscoped syntax?
[ ] -

-/
import Qq
import Qq.Match
import Lean
-- import Init.Data.String -- needed
-- import String
open Lean Elab Meta Term Meta Command Qq Match

def Ctx := List String

inductive Var : Ctx → Type
| zero : ∀ {Γ}, (s : String) -> Var (s :: Γ)
| succ : ∀ {Γ s}, Var Γ → Var (s :: Γ)

inductive Term : Ctx → Type
| const : ∀ {Γ}, String → Term Γ
| var : ∀ {Γ}, Var Γ → Term Γ
| lam : ∀ {Γ}, (s : String) → Term (s :: Γ) → Term Γ
| app : ∀ {Γ}, Term Γ → Term Γ → Term Γ

declare_syntax_cat lambda_scope
syntax ident : lambda_scope

-- it breaks when i change term to lambda_scope, i need to figure out how to fix that
syntax:10 (name := lambda_scoper) "<A" lambda_scope:10 "A>" : term
syntax "(" lambda_scope ")" : lambda_scope
syntax "<U" term:60 "U>" : lambda_scope
syntax:60 lambda_scope:60 lambda_scope:61 : lambda_scope
-- syntax lambda_scope lambda_scope+ : lambda_scope
syntax "λ" ident+ "." lambda_scope : lambda_scope

-- open String
def firstLetterCapital (s : String) : Bool :=
  Char.isUpper (String.front s)

/-
i'm trying to figure out how to match goals and hypotheses sanely.
there is https://github.com/leanprover-community/quote4
is that really the best solution? i should see if there is a standard answer
to the question of "what is the equivalent of an ltac tactic that matches for some hypothesis forms"
-/

def qqtest : Q(Nat) -> MetaM Q(Nat)
  | ~q($a + $b) => do return q($a)

def getCtx : Q(Type) -> MetaM Q(Ctx)
  | ~q(Term $ctx) => return q($ctx)

def getCtx2 (typ : Q(Type)) : MetaM Q(Ctx) :=
  match typ with
  | ~q(Term $ctx) => return q($ctx)

-- def test1 (typ : Expr) : MetaM Expr := do
--     let ~q(Term $ctx) := typ | throwError "bad"
--     _

partial def buildVarFromCtx (name : String) (ctx : Q(Ctx)) : MetaM Expr := -- MetaM Q(Var ctx) :=
  match ctx with
  | ~q(List.cons $name2 $rest) =>
    if name2 == Expr.lit (Literal.strVal name)
      then return q(@Var.zero $rest $name)
      else do let i : Q(Var $rest) <- buildVarFromCtx name q($rest)
              return q(@Var.succ $rest $name2 $i)
  | ~q(List.nil) => throwError "variable not found"
  | _ => throwError "variable not found"

def elabVarFromStringImpl (typ : Q(Type)) : MetaM Expr := do
  let ~q(Var $ctx) := typ | throwError "bad"
  return ctx

syntax (name := namedvarelab) "namedvar" ident : term

@[term_elab namedvarelab]
def elabVarFromString : TermElab := fun stx typ? => do
  -- TODO: try out the effect of having or not having this line
  tryPostponeIfNoneOrMVar typ?
  let some typ := typ? | throwError "expected type error"
  let `(namedvar $s:ident) := stx | throwError "something"
  let ctx <- elabVarFromStringImpl typ
  tryPostponeIfNoneOrMVar ctx
  buildVarFromCtx (toString s.getId) ctx

#eval (buildVarFromCtx "a" q("b" :: "a" :: List.nil))

-- TODO: https://leanprover-community.github.io/mathlib4_docs/Qq/Match.html refers to
-- something called "the builtin `match_expr` and `let_expr`", so what are those?


-- heavily referenced https://stackoverflow.com/questions/79575084/lean4-lambda-calculus-dsl-macro
macro_rules
  | `(<A λ $xs:ident* . $body:lambda_scope A>) => do
    let mut acc <- `(<A $body A>)
    for x in xs.reverse do
      acc <- `(Term.lam $(Lean.quote (toString x.getId)) $acc)
    return acc
  | `(<A $x:lambda_scope $xs:lambda_scope A>) => do
    `(Term.app (<A $x A>) (<A $xs A>))
  | `(<A $s:ident A>) =>
    let str := toString s.getId
    if firstLetterCapital str
      then `(Term.const $(Lean.quote str)) -- `(Term.const "he")
      else `(Term.var (namedvar $s))
  | `(<A ($t:lambda_scope) A>) => `(<A $t A>)
  -- | `(<A <U $t:term U> A>) => t -- Macro.throwError "thisd fklsdjf "

#reduce <A <U 5 U> A>
#reduce <A Z A>
#reduce <A (λ x y z . A) B C D A>
#reduce <A λ x. x A>
#reduce <A λ x . x A>
#reduce <A λ x . <U Var.zero "x" U> A>

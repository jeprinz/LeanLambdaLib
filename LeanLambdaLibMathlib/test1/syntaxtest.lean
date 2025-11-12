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

something: https://overreacted.io/a-lean-syntax-primer/

so there are a few things that can work.
[ ] - should i work with scoped or unscoped syntax?
[ ] -

-/
import Qq
import Qq.Match
import Lean
-- import Init.Data.String -- needed
-- import String
open Lean Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

def Ctx := List String

inductive Var : Ctx → String → Type
| zero : ∀ {Γ}, (s : String) -> Var (s :: Γ) s
| succ : ∀ {Γ s s'}, Var Γ s' → Var (s :: Γ) s'

inductive Term : Ctx → Type
| const : ∀ {Γ}, String → Term Γ
| var : ∀ {Γ}, (s : String) → Var Γ s → Term Γ
| lam : ∀ {Γ}, (s : String) → Term (s :: Γ) → Term Γ
| app : ∀ {Γ}, Term Γ → Term Γ → Term Γ

declare_syntax_cat lambda_scope
syntax ident : lambda_scope

-- it breaks when i change term to lambda_scope, i need to figure out how to fix that
syntax:10 (name := lambda_scoper) "<" lambda_scope:10 ">" : term
syntax "(" lambda_scope ")" : lambda_scope
syntax "{" term:10 "}" : lambda_scope
syntax:60 lambda_scope:60 lambda_scope:61 : lambda_scope
-- syntax lambda_scope lambda_scope+ : lambda_scope
syntax "λ" ident+ ". " lambda_scope : lambda_scope

-- open String
def firstLetterCapital (s : String) : Bool :=
  Char.isUpper (String.front s)

partial def buildVarFromCtx (name : String) (ctx : Q(Ctx)) : MetaM Expr := -- MetaM Q(Var ctx) :=
  match ctx with
  | ~q(List.cons $name2 $rest) =>
    if name2 == Expr.lit (Literal.strVal name)
      then return q(@Var.zero $rest $name)
      else do let i : Q(Var $rest $name) <- buildVarFromCtx name q($rest)
              return q(@Var.succ $rest $name2 $name $i)
              -- return q(@Var.succ $rest $name2 $i)
  | ~q(List.nil) => throwError "variable not found"
  | _ => throwError (String.join ["variable `", name, "' not found"])

def elabVarFromStringImpl (typ : Q(Type)) : MetaM Expr := do
  let ~q(Var $ctx $name) := typ | throwError "bad"
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

elab "test_thingy1234" : term => do
  (buildVarFromCtx "a" q("b" :: "a" :: List.nil))

#eval (buildVarFromCtx "a" q("b" :: "a" :: List.nil))
#eval test_thingy1234
#eval (namedvar x : Var ("y" :: "x" :: List.nil) _)

-- TODO: https://leanprover-community.github.io/mathlib4_docs/Qq/Match.html refers to
-- something called "the builtin `match_expr` and `let_expr`", so what are those?


-- heavily referenced https://stackoverflow.com/questions/79575084/lean4-lambda-calculus-dsl-macro
macro_rules
  | `(< λ $xs:ident* . $body:lambda_scope >) => do
    let mut acc <- `(< $body >)
    for x in xs.reverse do
      acc <- `(Term.lam $(Lean.quote (toString x.getId)) $acc)
    return acc
  | `(< $x:lambda_scope $xs:lambda_scope >) => do
    `(Term.app (< $x >) (< $xs >))
  | `(< $s:ident >) =>
    let str := toString s.getId
    if firstLetterCapital str
      then `(Term.const $(Lean.quote str))
      else `(Term.var $(Lean.quote str) (namedvar $s))
  | `(< ($t:lambda_scope) >) => `(< $t >)
  | `(< { $t:term } >) => `($t)

axiom freeterm : ∀{Γ}, Term Γ

#reduce < { 5 } >
#reduce < Z >
#reduce < (λ x y z . A) B C D >
#reduce < λ x. x >
#reduce < λ x . x >
#reduce < λ x . { Term.var "x" (Var.zero "x") } >
#reduce < λ x . ABCD >
#reduce < λ x y z . y >
#reduce < λ x. {freeterm} >

-- https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html

#check (Syntax.ident SourceInfo.none ("sdf".toSubstring) (Name.mkSimple "sdf"))

@[app_unexpander Term.const]
def unexpandConst : Unexpander
  | `($_const $x:str) =>
    let str := x.getString
    let name : Syntax := mkIdent $ Name.mkSimple str
    let tname : TSyntax _ := {raw := name}
    `(< $tname >)
  | _ => throw ()

@[app_unexpander Term.lam]
def unexpandLam : Unexpander
  | `($_  $name:str $body) =>
    let ident := mkIdent $ Name.mkSimple name.getString
    match body with
    | `(< λ $idents:ident* . $body2 >) => `(< λ $ident $idents* . $body2 >) -- this case handles nested lambdas
    | `(< $inside >) => `(< λ $ident . $inside >)
    | `( $inside ) => `(< λ $ident . {$inside} >)
    -- | _ => throw ()
  | _ => throw ()

inductive ParenKind :=
| None
| Parens
| Braces

open ParenKind

@[app_unexpander Term.app]
def unexpandApp : Unexpander
  -- | `($_ (< $a:lambda_scope > : term) (< $b:lambda_scope > : term)) =>
  | `($_ $a_term $b_term) =>
    let a_in := match a_term with
      | `(< $a >) => a
      | _ => TSyntax.mk Syntax.missing
    let b_in := match b_term with
      | `(< $b >) => b
      | _ => TSyntax.mk Syntax.missing
        -- we need to decide when to add parentheses.
        -- if a is lambda parenth it, if b is app or lambda parenth it
    let parena := match a_term with
      | `(< λ $_xs:ident* . $_body:lambda_scope >) => Parens
      | `(< $_any >) => None
      | _ => Braces
    let parenb := match b_term with
      | `(< λ $_xs:ident* . $_body:lambda_scope >) => Parens
      | `(< $_x:lambda_scope $_xs:lambda_scope >) => Parens
      | `(< $_any >) => None
      | _ => Braces
    -- because we can only match on things and construct syntax in the term category and not
    -- the lambda_scope category, there is no way to avoid this code repetition.
    match parena, parenb with
    | Parens, Parens => `(< ($a_in) ($b_in) >)
    | Parens, None => `(< ($a_in) $b_in >)
    | None, Parens => `(< $a_in ($b_in) >)
    | None, None => `(< $a_in $b_in >)
    | Braces, Braces => `(< {$a_term} {$b_term} >)
    | Braces, Parens => `(< {$a_term} ($b_in) >)
    | Braces, None => `(< {$a_term} $b_in >)
    | Parens, Braces => `(< ($a_in) {$b_term} >)
    | None, Braces => `(< $a_in {$b_term} >)
  | _ => throw ()

-- @[delab app.Term.var]
-- def delabVar : Delab := do
--   -- let e <- getExpr
--   `(1)
@[app_unexpander Term.var]
def unexpandVar : Unexpander
  | `($_var $x:str $_dontcare) =>
    let str:= x.getString
    let name : Syntax := mkIdent $ Name.mkSimple str
    let tname : TSyntax _ := {raw := name}
    `(< $tname >)
  | _ => throw ()

#reduce < λ x y z . ABCD >
#reduce <A B>
#check (Term.var "a" (Var.zero "a"))
#reduce <λ x . x>
#reduce <A (B C)>
#reduce <(λ x . x) A>
#reduce <(λ x y . x) (λ a b c . a (b c))>
#reduce <λ x. {freeterm}>
#reduce <{freeterm} A {freeterm}>
#reduce <{123}>
#reduce <A {freeterm}>

/-
there are things called the "parenthesizer" and "formatter"
see https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html
however, i have not been able to find any documentation or examples.
the only option is to read the source code.
i have gotten around the need for the parenthesizer by programming the unexpander for app to
insert parentheses. but it might be nicer to use a parenthesizer, and i still haven't got whitespace
good which would require the formatter.

i need to use the {} notation for printing.
the issue is that when it comes to unexpanding and delaborating, all of the unexpanders and delaborators
have to be based on a specific function name. but actually i want it to be more of a default case
that can work on anything.
maybe there is a way to have it work on variables?
-/

-- in this version, the names are ONLY going on the lambdas, not the context or variables.

import Qq
import Qq.Match
import Lean
-- import Init.Data.String -- needed
-- import String
open Lean Elab Meta Term Meta Command Qq Match PrettyPrinter Delaborator SubExpr

def Ctx := Nat

inductive Var : Ctx → Type
| zero : ∀ {Γ}, Var (Nat.succ Γ)
| succ : ∀ {Γ}, Var Γ → Var (Nat.succ Γ)

inductive LTerm : Ctx → Type
| const : ∀ {Γ}, String → LTerm Γ
| var : ∀ {Γ}, Var Γ → LTerm Γ
| lam : ∀ {Γ}, (s : String) → LTerm (Nat.succ Γ) → LTerm Γ
| app : ∀ {Γ}, LTerm Γ → LTerm Γ → LTerm Γ

declare_syntax_cat lambda_scope
syntax ident : lambda_scope

syntax:10 (name := lambda_scoper) "<" lambda_scope:10 ">" : term
syntax "(" lambda_scope ")" : lambda_scope
syntax "{" term:10 "}" : lambda_scope -- TODO: big-weaken thing!
syntax:60 lambda_scope:60 lambda_scope:61 : lambda_scope
syntax "λ" ident+ ". " lambda_scope : lambda_scope

def firstLetterCapital (s : String) : Bool :=
  Char.isUpper (String.front s)

partial def elabTermImpl (e : Syntax) (Γ : Q(Ctx)) (varnames: List String) : MetaM Q(LTerm $Γ) :=
  match e with
  | `(< $a:lambda_scope $b:lambda_scope >) => do
    let aarg <- `(< $a >)
    let barg <- `(< $b >)
    let ae <- elabTermImpl aarg Γ varnames
    let be <- elabTermImpl barg Γ varnames
    return q(@LTerm.app $Γ $ae $be)
  | `(< $s:ident >) =>
    let str := toString s.getId
    let strlit : Q(String) := Expr.lit (.strVal str)
    if firstLetterCapital str
      then return q(@LTerm.const $Γ $strlit)
      else throwError "todo2"
  | `(< λ $xs:ident* . $body:lambda_scope >) => do
    let mut varnames := varnames
    let mut recΓ := Γ
    for x in xs.reverse do
      varnames := (toString x.getId) :: varnames
      recΓ := q(Nat.succ $recΓ)
    let bodyarg <- `(< $body >)
    let mut acc <- elabTermImpl bodyarg recΓ varnames
    for x in xs.reverse do
      -- acc := q(Term.lam $test1 $thing)
      recΓ := q(Nat.succ $recΓ)
    return acc
  | _ => throwError "other"
  -- | _ => throwError (e.) -- return q(Term.const "not const")

def lookupVarInList (name : String) (varnames : List String) : MetaM (TSyntax `term) :=
  match varnames with
  | List.nil => throwError (String.join ["variable `", name, "' not found"])
  | List.cons name' rest => if name == name'
    then `(Var.zero)
    else do
      let i <- lookupVarInList name rest
      `(Var.succ $i)

-- an idea would be to have it produce syntax, and then only afterwards elaborate it back to a term
-- with Term.elabTerm
partial def elabTermImplS (e : Syntax) (varnames: List String) : MetaM (TSyntax `term) :=
  match e with
  | `(< $a:lambda_scope $b:lambda_scope >) => do
    let aarg <- `(< $a >)
    let barg <- `(< $b >)
    let ae : TSyntax `term <- elabTermImplS aarg varnames
    let be <- elabTermImplS barg varnames
    `(LTerm.app $ae $be)
  | `(< $s:ident >) =>
    let str := toString s.getId
    let strlit : TSyntax `term := Lean.quote (str)
    if firstLetterCapital str
      then `(LTerm.const $strlit)
      else do
        let i <- lookupVarInList str varnames
        `(LTerm.var $i)
  | `(< λ $xs:ident* . $body:lambda_scope >) => do
    let mut varnames := varnames
    for x in xs.reverse do
      varnames := (toString x.getId) :: varnames
    let bodyarg <- `(< $body >)
    let mut acc <- elabTermImplS bodyarg varnames
    for x in xs.reverse do
      acc <- `(LTerm.lam $(Lean.quote (toString x.getId)) $acc)
    return acc
  | `(< ( $t:lambda_scope ) >) => do
    let ts <- `(< $t >)
    elabTermImplS ts varnames
  | _ => throwError "other"

def getCtx (typ : Q(Type)) : MetaM Q(Ctx) := do
  let ~q(LTerm $ctx) := typ | throwError "bad"
  return ctx

@[term_elab lambda_scoper]
def elabTerm : TermElab := fun stx typ? => do
  let typ := match typ? with
    | Option.some typ => typ
    | Option.none => q(LTerm Nat.zero) -- TODO: can i make the ctx a fresh metavar instead?
  let ctx <- getCtx typ
  let `(< $_t >) := stx | throwError "this thing bla"
  -- elabTermImpl stx ctx []
  let res <- (elabTermImplS stx [])
  Term.elabTerm res (Option.some q(LTerm $ctx))

#reduce < λ x y . A B >
#reduce < λ x y . x y >
-- #reduce <λ x y . z >
#reduce < Z >
#reduce < (A) >
#reduce <(A B) C>
#reduce <A (B C)>
#reduce < (λ x y z . A) (B C) D >
#reduce < λ x. x >
#reduce < λ x . x >
#reduce < λ x . ABCD >
#reduce < λ x y z . y >

-- TODO: this syntax should actually apply to the quotiented terms instead of the deep embedding.
-- i do need to make sure that the pretty-printing can work with this encoding though

-- the Nat.zero is just a dummy to make it stop complaining about type errors
-- def ppTermImpl (t : Q(LTerm Nat.zero)) (varnames : List String) : MetaM (TSyntax `term) := do
def ppTermImpl (t : Expr) (varnames : List String) : MetaM (TSyntax `term) := do
  `(yesyesyes)
  -- match t with
  -- | ~q(LTerm.lam $s $t) => `(here3)
  -- | ~q(LTerm.const $s:str) => `(here1)
  --   -- let s' : Expr := s
  --   -- match s' with
  --   -- | Expr.lit _sadf => `(is literal)
  --   -- | _ => `(is not literal)
  -- | ~q(LTerm.var $i) => `(here2)
  --   -- do
  --   --   -- let str:= x.getString
  --   --   let str:= "example"
  --   --   let name : Syntax := mkIdent $ Name.mkSimple str
  --   --   let tname : TSyntax _ := {raw := name}
  --   --   `(< $tname >)
  -- | ~q(LTerm.app $t1 $t2) => `(here4)

-- we can only trigger delaborators for top level things. so we need one for each constructor
@[delab app.Term.app]
def delabApp : Delab := do
  let e <- getExpr
  ppTermImpl e []
@[delab app.Term.lam]
def delabLam : Delab := do
  let e <- getExpr
  ppTermImpl e []
@[delab app.Term.const]
def delabConst : Delab := do
  let e <- getExpr
  ppTermImpl e []
@[delab app.Term.var]
def delabVar : Delab := do
  let e <- getExpr
  ppTermImpl e []

#reduce <A>
#reduce <A B>
#reduce <λ x . x>

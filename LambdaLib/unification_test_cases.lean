import LambdaLib.qterm
import LambdaLib.unification

open QuotTerm

example (t1 t2 : QTerm)
  (H : < (λ x. x) {t1} > = <λ x. x>)
  : <{t1} {t2}> = t2 := by
  lambda_solve
  --

example (H : <λ x. A> = <λ x. B>) : False := by
  lambda_solve

example (H : <λ x. A> = <λ x. x>) : False := by
  lambda_solve

example (t1 t2 : QTerm) (H : <A {t1} > = <A {t2} >) : t1 = t2 := by
  lambda_solve
  --

example (H : <A B> = <A C>) : False := by
  lambda_solve

example (H : <A> = <B C>) : False := by
  lambda_solve

abbrev zero := <λ s z. z>
abbrev succ := <λ n. λ s z. s (n s z)>
abbrev plus := <λ a b. a {succ} (b {succ} {zero})>
abbrev mult := <λ a b. a (b {succ}) {zero}>

abbrev one := <{succ} {zero}>
abbrev two := <{succ} ({succ} {zero})>
abbrev four := <{succ} ({succ} {two})>


example : <{plus} {zero} {zero}> = zero := by
  lambda_solve
  --

example : <{plus} {one} {one}> = two := by
  unfold plus one two succ zero
  lambda_solve

example : <{plus} {two} {two}> = four := by
  unfold plus two succ zero four
  lambda_solve

-- NOTE: it seems like abbrevs are more useful if they are not nested,
-- otherwise some unfolds are necessary anyway
abbrev two2 := <λ s z. s (s z)>
abbrev four2 := <λ s z. s (s (s (s z)))>
example : <{plus} {two2} {two2}> = four2 := by
  lambda_solve
  --

example : <{mult} {zero} {zero}> = zero := by
  lambda_solve

example : <{mult} {one} {one}> = one := by
  unfold mult succ one
  lambda_solve
  --

example : <{mult} {two} {two}> = four := by
  unfold two four mult succ zero
  lambda_solve
  --

-- TODO: consider removing liftMultiZero? it shouldn't always go.
example : <λ x. {plus} {zero} {zero}> = <λ x. {zero}> := by
  lambda_solve
  --

/-
note that we don't need a rule that combines two nested liftMultis.
this is because either there is a lambda between them, in which case
one of the liftMulti_*_rw rules eliminates the outer one,
or there isn't, in which case the liftMultiZero rule eliminates the inner one.
-/

example (t1 t2 : QTerm)
  (H : <A B C> = <A {t1} {t2} >)
  : <Res {t1} {t2}> = <Res B C> := by
  lambda_solve
  --

example (t : Prod QTerm QTerm)
  (H : <A B C> = <A {t.1} {t.2} >)
  : <Res {t.1} {t.2}> = <Res B C> := by
  lambda_solve

example (t : Prod QTerm QTerm)
  (H : <A B C> = <A {t.1} {t.2} >)
  : t = ⟨<B>, <C>⟩ := by
  lambda_solve

-- TODO: make this not bad (if this works, then i can get rid of
-- Pmatch2 and just do Pmatch with a product type)
example (t1 t2 : QTerm × QTerm)
  (H1 : <A B C> = <A {t1.1} {t1.2} >)
  (H2 : <A B C> = <A {t2.1} {t2.2} >)
  : t1 = t2 := by
  lambda_solve

-- TODO: make this work better
example (t1 t2 t1' t2' : QTerm)
  (H1 : <A B C> = <A {t1} {t2} >)
  (H2 : <A B C> = <A {t1'} {t2'} >)
  : t1 = t1' := by
  lambda_solve

example (B C : QTerm) (H : <(λ x y z. A x y z) {B} D E> = <(λ x y z . A x y z) {C} D E>)
  : B = C := by
  lambda_solve

example (I C : QTerm)
  (H : <(λ x y z. A x y z) {I} D E> = <(λ x y z . A x y z) (λ x. x) D E>)
  (H2 : <{I} C> = <Result>)
  : C = <Result> := by
  lambda_solve

-- eta expansion
example : <λ x . A x> = <A> := by
  lambda_solve

example : <λ x y . A x y> = <A> := by
  lambda_solve

example : <λ x y z . A x y z> = <A> := by
  lambda_solve

example : <λ x y z w . A x y z w> = <A> := by
  lambda_solve

example (t : QTerm) : <λ x . {t} x> = t := by
  lambda_solve

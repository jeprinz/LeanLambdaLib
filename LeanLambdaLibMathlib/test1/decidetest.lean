-- https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/#decidable-propositions
-- https://leanprover-community.github.io/extras/simp.html

inductive CoolPred : Nat -> Prop where
| cp10 : CoolPred 10
| cpS : ∀{n}, CoolPred n → CoolPred (Nat.succ  n)

axiom A : Type
axiom a1 : A
axiom a2 : A
axiom a3 : A
axiom p : CoolPred 10 -> a1 = a2
axiom p2 : CoolPred 11 -> a1 = a2

instance coolPred10Decide : Decidable (CoolPred 10) :=
  isTrue CoolPred.cp10

example : CoolPred 10 := by
  decide -- this fails without the typeclass instance
  --

example : a1 = a2 := by
  --
  simp (disch := decide) [p] -- this fails without the typeclass instance

--- OK so that works, but now...

-- instance coolPredSDecide {n} (H : CoolPred n) : Decidable (CoolPred (Nat.succ n)) :=
--   isTrue (CoolPred.cpS H)

instance coolPredSDecide {n} (H : CoolPred n) : Decidable (CoolPred (Nat.succ n)) :=
  isTrue (CoolPred.cpS H)

-- maybe look up an example for
-- can i dispatch on other tactics?
macro "my_decide" : tactic => `(tactic| repeat (first | apply CoolPred.cp10 | apply CoolPred.cpS))

example : CoolPred 11 := by
  my_decide
  --

example : a1 = a2 := by
  --
  simp (disch := my_decide) [p2]
  --

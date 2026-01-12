import Mathlib.Tactic


example (h : ∀ (x : Nat), x = 5 → True) : True := by
  eapply h
  rfl
  -- no goals
-- (kernel) declaration has metavariables '_example'

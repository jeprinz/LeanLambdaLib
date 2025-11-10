-- In my coq axiomatization of quotients, I ran into an issue with type levels.
-- I want to see if Lean's quotients have this same problem.

inductive Example1 : Type 2 where
| ctr : {X : Type} -> X -> Example1

-- I suspect that the issue doesn't exist because Lean doesn't make definitions automatically
-- polymorphic over type levels like coq does.

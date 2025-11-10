theorem equality : 1 + 1 = 2 := by
  rfl

theorem testRewriteThing : 1 + _ = 2 := by
  rewrite [equality]
  rfl
  -- So it seems that lean's rewrite also specializes metavariables...

theorem testRewriteThing2 :  _ = 2 := by
  rewrite [equality]
  rfl
  -- Same behavior as rocq here. It doesns't do it if the entire expression is a metavar.

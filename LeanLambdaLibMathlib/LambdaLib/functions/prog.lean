-- from prog2.v in my rocq version

inductive Prog (A B : Type) : Type 2 where
| Ret : Option B → Prog A B
| Rec : ∀ (I : Type), (I → A) → ((I → B) → Prog A B) → Prog A B

inductive runProgR {A B : Type} (prog : A → Prog A B) : Prog A B → B → Prop where
| retR : ∀ (b), runProgR prog (.Ret (Option.some b)) b
| recR : ∀ I (args : I → A) (recVals : I → B) (res : B)
  (rest : (I → B) → Prog A B),
  -- if for all inputs of the form (args i), recVals describes the recursive calls
  (∀ (i : I), runProgR prog (prog (args i)) (recVals i))
  -- and given the results of those recursive calls, the program outputs `res'
  → runProgR prog (rest recVals) res
  -- then overall the results is `res'
  → runProgR prog (.Rec I args rest) res

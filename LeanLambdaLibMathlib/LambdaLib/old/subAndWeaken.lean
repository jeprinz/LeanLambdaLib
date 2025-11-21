/-
in this file, i'll define substitution and renamings on my terms.
i want to design these in a way that is fast for a small-step normalization of terms.
in my rocq version, i had single substitutions and weakenings.
this worked ok, but there is an issue when canceling subsittutions and weakenings;
there could me multiple weakenings in any order, and so the weakenins had to be cycled to find
if any could cancel with the substitution.

therefore, here i will make the weakenings
-/

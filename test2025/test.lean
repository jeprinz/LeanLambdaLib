def a : Type 1 := Type 0

def b : Type 0 := Nat -> Prop

inductive Box1 (T : Type 0) : Type 1 :=
| box : T -> Box1 T

-- This isn't allowed
-- inductive Box2 (T : Type 2) : Type 1 :=
-- | box : T -> Box2 T

-- def c : Type 0 := (Type 5 -> Prop) -> Nat
def d : Prop := (Type 10 -> Prop) -> True

-- Could this be allowed in a consistent type theory?
-- def e : Type 0 := (Type 0 -> Prop) -> Nat

def example1 : Type 0 := Subtype (fun (x : Nat) => x = x)

-- Could this be allowed ever?
def Group : Type 0 := Subtype (fun (G : Type 0) => G = G)

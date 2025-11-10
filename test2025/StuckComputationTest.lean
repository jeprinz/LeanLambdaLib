namespace DemonstrateProblem
  axiom Q : Type
  axiom a : Q
  axiom b : Q
  axiom p : a = b

  inductive data : Q -> Type
  | yes : data a
  | no : data b

  def transport {T : Type} {a b : T} (P : T -> Type) (p : a = b) : P a -> P b :=
    fun pa => match p with
              | Eq.refl _ => pa

  def data_not {q : Q} (d : data q) : data q :=
    match d with
    | data.yes => transport data (Eq.symm p) data.no
    | data.no => transport data p data.yes

  theorem test1 : data_not data.no = transport data p data.yes := by
    simp
    unfold data_not
    simp

  theorem test : data_not (data_not data.no) = data.no := by
    --
    rewrite [test1]
    unfold transport
    simp
    rfl
    sorry
    -- For some reason the thing that works in WhyDoesItWorkHere namespace below

  #eval (1 + 2)
  -- #normalize (data_not data.yes)

namespace WithQuotient
  def boolRel : Bool -> Bool -> Prop := fun _ _ => True
  def Q : Type := Quot boolRel
  def a : Q := Quot.mk boolRel true
  def b : Q := Quot.mk boolRel false
  def p : a = b := Quot.sound True.intro

  inductive data : Q -> Type
  | yes : data a
  | no : data b

  def transport {T : Type} {a b : T} (P : T -> Type) (p : a = b) : P a -> P b :=
    fun pa => match p with
              | Eq.refl _ => pa


  def data_not {q : Q} (d : data q) : data q :=
    match d with
    | data.yes => transport data (Eq.symm p) data.no
    | data.no => transport data p data.yes

  theorem test1 : data_not data.no = transport data p data.yes := by
    simp
    unfold data_not
    simp
    --

  theorem test : data_not (data_not data.no) = data.no := by
    rewrite [test1]
    simp
    unfold transport
    simp -- this works even though p is an axiom????
    rfl

namespace WhyDoesItWorkHere
  def Q : Type := Nat
  def a : Q := Nat.zero
  def b : Q := Nat.zero
  -- def b : Q := Nat.succ Nat.zero
  -- def p : a = b := rfl
  axiom p : a = b

  inductive data : Q -> Type
  | yes : data a
  | no : data b

  def transport {T : Type} {a b : T} (P : T -> Type) (p : a = b) : P a -> P b :=
    fun pa => match p with
              | Eq.refl _ => pa


  def data_not {q : Q} (d : data q) : data q :=
    match d with
    | data.yes => transport data (Eq.symm p) data.no
    | data.no => transport data p data.yes

  theorem test1 : data_not data.no = transport data p data.yes := by
    simp
    unfold data_not
    simp
    --

  theorem test : data_not (data_not data.no) = data.no := by
    rewrite [test1]
    simp
    unfold transport
    unfold a
    unfold b
    simp -- this works even though p is an axiom????
    -- I figured out why this works - its because a is actually definitionally equal to b
    -- because they are both defined as 0. If they are defined as definitionally unequal,
    -- then this doesn't work.
    rfl

  def asdf := 1

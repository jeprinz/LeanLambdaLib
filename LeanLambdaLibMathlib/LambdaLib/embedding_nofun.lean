import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic

open QuotTerm

-- in this file, i'll define dependent type theory and prove canonicity

namespace S
abbrev pair := <λ t1 t2 p. p t1 t2>
abbrev proj1 := <λ p. p (λ x y. x)>
abbrev proj2 := <λ p. p (λ x y. y)>
-- TODO: i can make syntax for pair with a macro, which will run before the elaborator!

-- contexts
abbrev nil := <Nil>
abbrev cons := <Cons> -- takes ctx, lvl, and type

-- variables
abbrev zero := <λ env. {proj2} env>
abbrev succ := <λ x env. x ({proj1} env)>

abbrev pi := <λ x y env. Pi (x env) (λ a. y ({pair} env a))>
abbrev U := <λ env. U>
abbrev Empty := <λ env. Empty>
abbrev Lift := <λ T env. Lift (T env)>

abbrev lambda := <λ t env a. t ({pair} env a)>
abbrev app := <λ t1 t2 env. (t1 env) (t2 env)>

abbrev weaken := <λ t env. t ({proj1} env)>
abbrev subLast := <λ t toSub env. t ({pair} env (toSub env))>
end S

inductive VarTyped : QTerm → Nat → QTerm → QTerm → Prop where
| zero : ∀{ctx T lvl},
  VarTyped <{S.cons} {ctx} {const (.natConst lvl)} {T}> lvl <{S.weaken} {T}> zero
| succ : ∀{ctx A T s lvl1 lvl2}, VarTyped ctx lvl1 A s
  → VarTyped <{S.cons} {ctx} {lvl2} {T}> lvl1 <{S.weaken} {A}> <{succ} {s}>

-- context → level → type → term → prop
inductive Typed : QTerm → Nat → QTerm → QTerm → Prop where
| lambda : ∀{ctx A B s lvl},
  Typed ctx (Nat.succ lvl) S.U <{S.pi} {A} {B}>
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl B s
  → Typed ctx lvl <{S.pi} {A} {B}> <{S.lambda} {s}>
| app : ∀{ctx A B s1 s2 lvl}, Typed ctx lvl <{S.pi} {A} {B}> s1 → Typed ctx lvl A s2
  → Typed ctx lvl <{S.subLast} {B} {s2}> <{S.app} {s1} {s2}>
| var : ∀{ctx T t lvl}, VarTyped ctx lvl T t → Typed ctx lvl T t
| Empty : ∀{ctx}, Typed ctx 1 S.U S.Empty
| U : ∀{ctx lvl}, Typed ctx (2 + lvl) S.U S.U
| Pi : ∀{ctx lvl A B}, Typed ctx lvl.succ S.U A
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl.succ S.U B
  → Typed ctx lvl.succ S.U <{S.pi} {A} {B}>
| Lift : ∀{ctx lvl T}, Typed ctx (1 + lvl) S.U T → Typed ctx (2 + lvl) S.U <{S.Lift} {T}>
| lift : ∀{ctx lvl T t}, Typed ctx lvl T t → Typed ctx (1 + lvl) <{S.Lift} {T}> t
| lower : ∀{ctx lvl T t}, Typed ctx (1 + lvl) <{S.Lift} {T}> t → Typed ctx lvl T t

inductive In' (prev : QTerm → (QTerm → Prop) → Prop) : QTerm → (QTerm → Prop) → Prop where
| in_Pi : ∀ (s : QTerm → Prop) (F : QTerm → (QTerm → Prop)) A B,
  In' prev A s
  → (∀ a, s a → In' prev <{B} {a}> (F a))
  → In' prev <Pi {A} {B}> (fun f ↦ ∀ a, s a → F a <{f} {a}>)
| in_Empty : In' prev <Empty> (fun _ ↦ False)
| in_Type : In' prev <U> (fun T ↦ ∃ S, prev T S)
| in_Lift : ∀ T S, prev T S → In' prev <Lift {T}> S

def In (lvl : Nat) : QTerm → (QTerm → Prop) → Prop :=
  match lvl with
  | .zero => fun _ _ ↦ False
  | .succ lvl' => In' (In lvl')

inductive In_ctx : QTerm → QTerm → Prop where
| in_nil : In_ctx S.nil S.nil
| in_cons : ∀ {env ctx lvl val T s},
  In_ctx env ctx
  → In (.succ lvl) <{T} {env}> s
  → s val
  → In_ctx <{S.pair} {env} {val}> <{S.cons} {ctx} {const (.natConst lvl)} {T}>

-- why lean, why is this not in the standard library
theorem forall_ext.{u} (A : Sort u) (B B' : A → Prop) (_ : ∀ a, B a = B' a)
  : (∀ a, B a) = (∀ a, B' a) := by grind

theorem In_function {lvl T S1 S2} (out1 : In lvl T S1) (out2 : In lvl T S2) : S1 = S2 := by
  induction lvl generalizing T S1 S2 with
  | zero =>
    grind only [In]
  | succ lvl' ih =>
    induction out1 generalizing S2 with
    | in_Empty =>
      generalize h : <Empty> = x at out2
      cases out2 <;> lambda_solve
    | in_Type =>
      generalize h : <U> = x at out2
      cases out2 <;> lambda_solve
    | in_Lift T S uh =>
      generalize h : <Lift {T}> = x at out2
      cases out2 <;> try lambda_solve
      apply ih <;> assumption
    | in_Pi s F A B x y ih_s ih_F =>
      generalize h : <Pi {A} {B}> = x at out2
      generalize s2eq : S2 = S2' at out2
      induction out2 with | in_Pi s' F' A' B' InA's' InB'aF' _ _ => _ | _ <;> lambda_solve
      rw [<- @ih_s s' InA's'] at *
      apply funext; intros f
      apply forall_ext; intros a
      apply forall_ext; intros Sa
      rw [@ih_F a Sa (F' a) (InB'aF' a Sa)]

theorem fundamental_lemma {ctx T lvl t env}
  (mT : Typed ctx lvl T t)
  (mctx : In_ctx env ctx)
  : ∃ s, In (.succ lvl) <{T} {env}> s ∧ s <{t} {env}>
  :=
  match mT with
  -- | @Typed.lambda ctx A B s lvl tyAB body => by
  --   have ⟨sAB, InSAB, SaAB⟩ := fundamental_lemma tyAB mctx
  --   generalize why : <{S.U} {env}> = thing at InSAB
  --   cases InSAB <;> (try lambda_solve <;> fail)
  --   rcases SaAB with ⟨SAB, InABS⟩
  --   generalize why2 : <{S.pi} {A} {B} {env}> = thing2 at InABS
  --   cases InABS with | in_Pi SA SB A' B' InA InB => _ | _ <;> try (lambda_solve <;> fail)
  --   exists (fun f ↦ ∀ a, SA a → SB a <{f} {a}>)
  --   apply And.intro
  --   · apply @In'.in_Pi (In lvl) SA SB A' B' InA InB
  --   · simp
  --     intros a SAa
  --     lambda_solve
  --     rcases fundamental_lemma body (In_ctx.in_cons mctx InA SAa) with ⟨SBa, InSBa, thing⟩
  --     normalize
  --     rw [<- In_function InSBa (InB a SAa)]
  --     assumption
  -- | @Typed.app ctx A B s1 s2 lvl t1 t2 => by
  --   rcases (fundamental_lemma t1 mctx) with ⟨S1, In1, S1s1⟩
  --   rcases (fundamental_lemma t2 mctx) with ⟨S2, In2, S2s2⟩
  --   generalize why2 : <{S.pi} {A} {B} {env}> = thing2 at In1
  --   cases In1 with | in_Pi SA SB A' B' InA InB => _ | _ <;> lambda_solve
  --   rw [In_function In2 InA] at *
  --   exists (SB <{s2} {env}>)
  --   have InB := InB _ S2s2
  --   lambda_solve
  --   apply InB
  | Typed.var _ => by sorry
  -- | Typed.Empty => by
  --   exists (fun T ↦ ∃ S, In 1 T S)
  --   apply And.intro
  --   · simp [In]
  --     lambda_solve
  --     apply In'.in_Type
  --   · simp [In]
  --     exists (fun _ ↦ False)
  --     lambda_solve
  --     apply In'.in_Empty
  | Typed.U => by sorry
  | @Typed.Pi ctx lvl A B a b => by
    have ⟨SA, InSA, SaA⟩ := fundamental_lemma a mctx
    generalize why1 : <{S.U} {env}> = x at InSA
    cases InSA <;> try (lambda_solve <;> fail)
    rcases SaA with ⟨SA, InSA⟩
    exists (fun T ↦ ∃ S, In lvl.succ T S)
    apply And.intro
    · apply In'.in_Type
    · simp [In] at *
      let F := fun a b ↦ ∃ SB, In lvl.succ <{B} ({S.pair} {env} {a})> SB ∧ SB b
      exists (fun f ↦ ∀ a, SA a → F a <{f} {a}>)
      normalize
      apply In'.in_Pi SA F _ _ InSA
      intros a SAa
      rcases fundamental_lemma b (In_ctx.in_cons mctx InSA SAa) with ⟨SBa, InSBa, SBaBa⟩
      generalize why : <{S.U} ({S.pair} {env} {a})> = thing at InSBa
      cases InSBa <;> lambda_solve
      rcases SBaBa with ⟨S, SBaBa⟩
      simp [In] at SBaBa
      suffices F a = S by subst S; assumption
      unfold F
      ext t
      normalize
      apply Iff.intro
      · rintro ⟨SB, InSB, SBt⟩
        rw [<- In_function InSB SBaBa]
        assumption
      · intros St
        exists S
  | Typed.Lift _ => by sorry
  | Typed.lift _ => by sorry
  | Typed.lower _ => by sorry
  | _ => by sorry

-- can i use the lambda functions to encode the logical predicate?

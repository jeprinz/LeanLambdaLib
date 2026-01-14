import LambdaLib.qterm
import LambdaLib.unification
import Mathlib.Tactic

open QuotTerm

-- in this file, i'm seeing if the freevars version works with this proof
-- multisubsitutions for In_Ctx are going to be the main issue

namespace S
-- contexts
abbrev nil := <Nil>
abbrev cons := <Cons> -- takes ctx, lvl, and type


abbrev pi (A B : QTerm) := app (app <Pi> A) (lam "a" B)
abbrev U := <U>
abbrev Empty := <Empty>
abbrev Lift (T : QTerm) := app <Lift> T

end S


inductive VarTyped : QTerm → Nat → QTerm → Nat → Prop where
| zero : ∀{ctx T lvl},
  VarTyped <{S.cons} {ctx} {const (.natConst lvl)} {T}> lvl (lift 0 T) 0
| succ : ∀{ctx A T s lvl1 lvl2}, VarTyped ctx lvl1 A s
  → VarTyped <{S.cons} {ctx} {lvl2} {T}> lvl1 (lift 0 A) s.succ

-- context → level → type → term → prop
inductive Typed : QTerm → Nat → QTerm → QTerm → Prop where
| lambda : ∀{ctx A B s lvl},
  Typed ctx (Nat.succ lvl) S.U (S.pi A B)
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl B s
  → Typed ctx lvl (S.pi A B) (lam "x" s)
| app : ∀{ctx A B s1 s2 lvl}, Typed ctx lvl (S.pi A B) s1 → Typed ctx lvl A s2
  → Typed ctx lvl (subst 0 s2 B) (app s1 s2)
| var : ∀{ctx T t lvl}, VarTyped ctx lvl T t → Typed ctx lvl T (var t)
| Empty : ∀{ctx}, Typed ctx 1 S.U S.Empty
| U : ∀{ctx} {lvl : Nat}, Typed ctx lvl.succ.succ S.U S.U
| Pi : ∀{ctx lvl A B}, Typed ctx lvl.succ S.U A
  → Typed <{S.cons} {ctx} {const (.natConst lvl)} {A}> lvl.succ S.U B
  → Typed ctx lvl.succ S.U (S.pi A B)
| Lift : ∀{ctx T} {lvl : Nat}, Typed ctx lvl.succ S.U T → Typed ctx lvl.succ.succ S.U (S.Lift T)
| lift : ∀{ctx lvl T t}, Typed ctx lvl T t → Typed ctx lvl.succ (S.Lift T) t
| lower : ∀{ctx lvl T t}, Typed ctx lvl.succ (S.Lift T) t → Typed ctx lvl T t

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

-- this needs a special `multiSubst` type
-- i've decided that i want to represent substs and lifts as fundamentally a sequence of substs and lifts
-- for now, i can simplify and represent as a list of QTerms, and then there will be multiSubst
-- that takes a list of QTerms and a QTerm and does the subst.
inductive In_ctx : (List QTerm) → QTerm → Prop where
| in_nil : In_ctx [] S.nil
| in_cons : ∀ {env ctx lvl val T s},
  In_ctx env ctx
  → In (.succ lvl) (substMulti 0 env T) s
  → s val
  → In_ctx (val :: env) <{S.cons} {ctx} {const (.natConst lvl)} {T}>

theorem fundamental_lemma {ctx T lvl t env}
  (mT : Typed ctx lvl T t)
  (mctx : In_ctx env ctx)
  : ∃ s, In (.succ lvl) (substMulti 0 env T) s ∧ s (substMulti 0 env t)
  :=
  match mT with
  | @Typed.lambda ctx A B s lvl tyAB body => by
    have ⟨sAB, InSAB, SaAB⟩ := fundamental_lemma tyAB mctx
    generalize why : (substMulti 0 env S.U) = thing at InSAB
    cases InSAB <;> (try lambda_solve <;> fail)
    rcases SaAB with ⟨SAB, InABS⟩
    generalize why2 : (substMulti 0 env (S.pi A B)) = thing2 at InABS
    cases InABS with | in_Pi SA SB A' B' InA InB => _ | _ <;> try (lambda_solve <;> fail)
    exists (fun f ↦ ∀ a, SA a → SB a <{f} {a}>)
    apply And.intro
    · apply @In'.in_Pi (In lvl) SA SB A' B' InA InB
    · simp
      intros a SAa
      normalize
      --
      lambda_solve
      rcases fundamental_lemma body (In_ctx.in_cons mctx InA SAa) with ⟨SBa, InSBa, thing⟩
      normalize
      rw [<- In_function InSBa (InB a SAa)]
      assumption
  -- | @Typed.app ctx A B s1 s2 lvl t1 t2 => by
  --   rcases (fundamental_lemma t1 mctx) with ⟨S1, In1, S1s1⟩
  --   rcases (fundamental_lemma t2 mctx) with ⟨S2, In2, S2s2⟩
  --   generalize why2 : <{S.pi} {A} {B} {env}> = thing2 at In1
  --   cases In1 with | in_Pi SA SB A' B' InA InB => _ | _ <;> try (lambda_solve <;> fail)
  --   normalize
  --   lambda_solve
  --   rw [In_function In2 InA] at *
  --   exists (SB <{s2} {env}>)
  --   have InB := InB _ S2s2
  --   lambda_solve
  --   apply InB
  -- | Typed.var x => by
  --   clear mT
  --   induction x generalizing env
  --     <;> generalize H : (< {S.cons} {_} {_} {_} >) = ctx2 at mctx
  --     <;> cases mctx <;> lambda_solve <;> grind
  -- | Typed.Empty => by
  --   exists (fun T ↦ ∃ S, In 1 T S)
  --   lambda_solve
  --   apply And.intro
  --   · simp [In]
  --     apply In'.in_Type
  --   · simp [In]
  --     exists (fun _ ↦ False)
  --     apply In'.in_Empty
  -- | @Typed.U ctx lvl => by
  --   exists (fun T ↦ ∃ S, In lvl.succ.succ T S)
  --   normalize
  --   apply And.intro
  --   · apply In'.in_Type
  --   · exists (fun T ↦ ∃ S, In lvl.succ T S)
  --     apply In'.in_Type
  -- | @Typed.Pi ctx lvl A B a b => by
  --   have ⟨SA, InSA, SaA⟩ := fundamental_lemma a mctx
  --   generalize why1 : <{S.U} {env}> = x at InSA
  --   cases InSA <;> try (lambda_solve <;> fail)
  --   rcases SaA with ⟨SA, InSA⟩
  --   exists (fun T ↦ ∃ S, In lvl.succ T S)
  --   apply And.intro
  --   · apply In'.in_Type
  --   · simp [In] at *
  --     let F := fun a b ↦ ∃ SB, In lvl.succ <{B} ({S.pair} {env} {a})> SB ∧ SB b
  --     exists (fun f ↦ ∀ a, SA a → F a <{f} {a}>)
  --     normalize
  --     apply In'.in_Pi SA F _ _ InSA
  --     intros a SAa
  --     rcases fundamental_lemma b (In_ctx.in_cons mctx InSA SAa) with ⟨SBa, InSBa, SBaBa⟩
  --     generalize why : <{S.U} ({S.pair} {env} {a})> = thing at InSBa
  --     cases InSBa <;> lambda_solve
  --     rcases SBaBa with ⟨S, SBaBa⟩
  --     simp [In] at SBaBa
  --     suffices F a = S by subst S; assumption
  --     unfold F
  --     ext t
  --     normalize
  --     apply Iff.intro
  --     · rintro ⟨SB, InSB, SBt⟩
  --       rw [<- In_function InSB SBaBa]
  --       assumption
  --     · intros St
  --       exists S
  -- | @Typed.Lift ctx T lvl Tty => by
  --   have ⟨s, InS, ST⟩ := fundamental_lemma Tty mctx
  --   generalize h : <{S.U} {env}> = x at InS
  --   cases InS <;> (try lambda_solve <;> fail)
  --   exists (fun T ↦ ∃ S, In lvl.succ.succ T S)
  --   simp [In]
  --   apply And.intro
  --   · apply In'.in_Type
  --   · have ⟨s, Ins⟩ := ST
  --     exists s
  --     normalize
  --     apply (In'.in_Lift _ _ Ins)
  -- | Typed.lift t => by
  --   have ⟨s, Ins, sT⟩ := fundamental_lemma t mctx
  --   exists s
  --   normalize
  --   apply (And.intro (In'.in_Lift _ _ Ins) sT)
  -- | Typed.lower t => by
  --   have ⟨s, Ins, sT⟩ := fundamental_lemma t mctx
  --   generalize h : <{S.Lift} {T} {env}> = x at Ins
  --   cases Ins <;> lambda_solve
  --   exists s
  | _ => sorry

-- -- can i use the lambda functions to encode the logical predicate?
-- theorem consistency {lvl val} : Typed S.nil lvl S.Empty val → False := by
--   intros t
--   rcases (fundamental_lemma t In_ctx.in_nil) with ⟨s, inS, sval⟩
--   generalize h : <{S.Empty} {S.nil}> = x at inS
--   cases inS <;> lambda_solve

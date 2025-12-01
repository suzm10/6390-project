import Std.Data.HashMap

-- Simple translation of STLC code from PLF with some additions

-- Just a symbolic name like 'a
-- The relationship between lifetimes is determined by the surrounding context.
abbrev Lifetime := String

inductive RefKind : Type where
  | shared : RefKind
  | mutable : RefKind
  deriving Repr

inductive Ty : Type where
  | unit : Ty
  | nat : Ty
  | bool : Ty
  | arrow : Ty → Ty → Ty
  -- NOTE: References store their lifetimes here, so the "lives for" predicate we're
  -- going to have in the refinements is implemented by simply comparing the lifetime
  -- associated with a reference...
  -- Hey, wait a second. A reference's lifetime is valid if the *value it points to* is valid.
  -- I still think it's smart to allow for this if you want to constrain its lifetime to be strictly
  -- the same as another associated reference that's in scope.
  -- Lifetime validity is constrained by the "place context"
  | ref : RefKind → Lifetime → Ty → Ty
  deriving Repr

inductive Term : Type where
  | var : String → Term
  | abs : String → Ty → Term → Term
  | app : Term → Term → Term
  | true : Term
  | false : Term
  | unit : Term
  | nat_const : Nat → Term
  | nat_succ : Term → Term
  | nat_pred : Term → Term
  | string_const : String → Term
  | if_then_else : Term → Term → Term → Term
  | ref : RefKind → Term → Term -- Unlike in STLC+Ref, this *borrows* as opposed to allocating.
  | deref : Term → Term
  | assign : Term → Term → Term -- NOTE: For simplicity, let's say you can only assign to the result of (deref mutable-reference)
  | loc : Nat → Term -- Returned from evaluating 
  deriving Repr

structure PlaceCtx where
  places : Array Term
  names : Std.HashMap String Nat
  deriving Repr

inductive Value : Term → Prop where
  | abs : ∀ x T₂ t₁,
      Value (Term.abs x T₂ t₁)
  | true : Value Term.true
  | false : Value Term.false
  | nat_const : ∀ n,
      Value (Term.nat_const n)
  | string_const : ∀ s,
      Value (Term.string_const s)
  | unit : Value Term.unit

def owned : Ty → Prop
  | Ty.ref _ _ _ => False
  | _ => True

-- substitute s for x in t as in [x := s]t
def subst (x : String) (s : Term) : Term → Term
  | Term.var y =>
      if x = y then s else Term.var y
  | Term.app t₁ t₂ =>
      Term.app (subst x s t₁) (subst x s t₂)
  -- either (y:T, [y:=s] t_1), y is bound so can't substitute
  -- or y is not bound (y:T, [x:=s] t₁)
  | Term.abs y T t₁ => Term.abs y T (if x = y then t₁ else (subst x s t₁))
  | Term.if_then_else t₁ t₂ t₃ =>
      Term.if_then_else (subst x s t₁) (subst x s t₂) (subst x s t₃)
  | Term.true =>  Term.true
  | Term.false => Term.false
  | Term.string_const s => Term.string_const s
  | Term.nat_const n => Term.nat_const n
  | Term.nat_succ t₁ => Term.nat_succ (subst x s t₁)
  | Term.nat_pred t₁ => Term.nat_pred (subst x s t₁)
  | Term.unit => Term.unit
  | Term.ref ℓ t₁ => Term.ref ℓ (subst x s t₁)
  | Term.deref t₁ => Term.deref (subst x s t₁)
  | Term.assign t₁ t₂ => Term.assign (subst x s t₁) (subst x s t₂)
  | t@(Term.loc _) => t

-- TODO: Store context (actually, I guess we ought to think about that right now)
-- A store context tracks all values created by `let`.
-- I don't think I want to open the can of worms of letting function arguments be mutable,
-- although it might not really be any different from 
inductive Step : Term → Term → Prop where
  | eval_appabs : ∀ x T₂ t₁ v₂,
      Value v₂ →
      Step (Term.app (Term.abs x T₂ t₁) v₂) (subst x v₂ t₁) -- [x:=v2]t1
  | eval_app1 : ∀ t₁ t₁' t₂,
      Step t₁ t₁' →
      Step (Term.app t₁ t₂) (Term.app t₁' t₂)
  | eval_app2 : ∀ v₁ t₂ t₂',
      Value v₁ →
      Step t₂ t₂' →
      Step (Term.app v₁ t₂) (Term.app v₁ t₂')
  -- number
  | eval_succnat : ∀ (n : Nat),
      Step (Term.nat_succ (Term.nat_const n)) (Term.nat_const (Nat.succ n))
  | eval_succ : ∀ t₁ t₁',
      Step t₁ t₁' →
      Step (Term.nat_succ t₁) (Term.nat_succ t₁')
  | eval_prednat : ∀ t₁ t₁',
      Step (Term.nat_pred (Term.nat_const n)) (Term.nat_const (Nat.pred n))
  | eval_pred : ∀ t₁ t₁',
      Step t₁ t₁' →
      Step (Term.nat_pred t₁) (Term.nat_pred t₁')
  -- bool
  | eval_if_true : ∀ t₁ t₂,
      Step (Term.if_then_else Term.true t₁ t₂) t₁
  | eval_if_false : ∀ t₁ t₂,
      Step (Term.if_then_else Term.false t₁ t₂) t₂
  | eval_if : ∀ t₁ t₁' t₂ t₃,
      Step t₁ t₁' →
      Step (Term.if_then_else t₁ t₂ t₃) (Term.if_then_else t₁' t₂ t₃)
  -- `st` is a "store context" which maps pointers to their underlying values.
  -- We're going to do something similar
  -- Would our typechecker need
  | eval_ref : ∀ t₁ t₁' st st',
    sorry


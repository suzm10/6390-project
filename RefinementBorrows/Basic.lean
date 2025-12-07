import Std.Data.HashMap

-- Simple translation of STLC code from PLF with some additions

-- Just a symbolic name like 'a
-- The relationship between lifetimes is determined by the surrounding context.
abbrev Lifetime := String

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
  | ref : Lifetime → Ty → Ty
  deriving Inhabited, Repr, BEq, Hashable

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
  | is_zero : Term → Term
  | string_const : String → Term
  | if_then_else : Term → Term → Term → Term
  | let_in : String → Ty → Term → Term → Term
  | box : Term → Term
  | ref_mut : Term → Term -- Unlike in STLC+Ref, this *borrows* as opposed to allocating. We also apply a refinement...
  | deref : Term → Term
  | assign : Term → Term → Term -- NOTE: For simplicity, let's say you can only assign to the result of (deref mutable-reference)
  | drop : Term → Term
  | loc : Nat → Term -- Returned from evaluating a reference to a variable name.
  deriving Repr, BEq, Hashable

-- Lean actually has a notion of "subtype" which appears very close to a refinement type, or at least uses very suggestive notation to imply that they are the same!
-- ...but I unfortunately can't store them in an array, so I guess I'll settle
-- for a structure that pairs one of our types with a proposition.
structure RTy where
  datatype : Ty
  refinement : Prop

-- "A store type is just a list of types that maps cell number to type."
-- We don't just have cells in this language though, so maybe we ought to try
-- something else instead -- maybe mapping something variable names?

abbrev PlaceCtx := Array (Option Term)
abbrev StoreTy := Array RTy
abbrev TyCtx := Std.HashMap Term RTy

inductive HasType (st : StoreTy) : TyCtx → Term → RTy → Prop where
  | var : ∀ Γ x T₁,
    Γ[x]? = some T₁ →
    HasType st Γ x T₁


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
  | Ty.ref _ _ => False
  | _ => True

-- substitute s for x in t as in [x := s]t
def subst (x : String) (s : Term) : Term → Term
  | .var y =>
      if x = y then s else Term.var y
  | .app t₁ t₂ =>
      .app (subst x s t₁) (subst x s t₂)
  -- either (y:T, [y:=s] t_1), y is bound so can't substitute
  -- or y is not bound (y:T, [x:=s] t₁)
  | .abs y T t₁ => .abs y T (if x = y then t₁ else (subst x s t₁))
  | .let_in y T t₁ t₂ => .let_in y T (subst x s t₁) (if x = y then t₂ else (subst x s t₂))
  | .if_then_else t₁ t₂ t₃ =>
      .if_then_else (subst x s t₁) (subst x s t₂) (subst x s t₃)
  | .true =>  .true
  | .false => .false
  | .is_zero t₁ => .is_zero (subst x s t₁)
  | .string_const s => .string_const s
  | .nat_const n => .nat_const n
  | .nat_succ t₁ => .nat_succ (subst x s t₁)
  | .nat_pred t₁ => .nat_pred (subst x s t₁)
  | .unit => .unit
  | .box t₁ => .box (subst x s t₁)
  | .ref_mut t₁ => .ref_mut (subst x s t₁)
  | .deref t₁ => .deref (subst x s t₁)
  | .assign t₁ t₂ => .assign (subst x s t₁) (subst x s t₂)
  | .drop t₁ => .drop (subst x s t₁)
  | t@(.loc _) => t

-- TODO: Store context (actually, I guess we ought to think about that right now)
-- A store context tracks all values created by `let`.
-- I don't think I want to open the can of worms of letting function arguments be mutable,
-- although it might not be any different from changing a let-binding.
inductive Step : (Term × PlaceCtx) → (Term × PlaceCtx) → Prop where
  | eval_appabs : ∀ x T₂ t₁ v₂ ctx,
      Value v₂ →
      Step ((.app (.abs x T₂ t₁) v₂), ctx) ((subst x v₂ t₁), ctx) -- [x:=v2]t1
  | eval_app1 : ∀ t₁ t₁' t₂ ctx ctx',
      Step (t₁, ctx) (t₁', ctx') →
      Step ((.app t₁ t₂), ctx) ((.app t₁' t₂), ctx')
  | eval_app2 : ∀ v₁ t₂ t₂' ctx ctx',
      Value v₁ →
      Step (t₂, ctx) (t₂', ctx') →
      Step ((.app v₁ t₂), ctx) ((.app v₁ t₂'), ctx')
  -- number
  | eval_succnat : ∀ (n : Nat) ctx,
      Step ((.nat_succ (.nat_const n)), ctx) ((.nat_const (Nat.succ n)), ctx)
  | eval_succ : ∀ t₁ t₁' ctx ctx',
      Step (t₁, ctx) (t₁', ctx) →
      Step ((.nat_succ t₁), ctx) ((.nat_succ t₁'), ctx')
  | eval_prednat : ∀ (n : Nat) ctx,
      Step ((.nat_pred (.nat_const n)), ctx) ((.nat_const (Nat.pred n)), ctx)
  | eval_pred : ∀ t₁ t₁' ctx ctx',
      Step (t₁, ctx) (t₁', ctx') →
      Step ((.nat_pred t₁), ctx) ((.nat_pred t₁'), ctx')
  -- bool
  | eval_if_true : ∀ t₁ t₂ ctx,
      Step ((.if_then_else .true t₁ t₂), ctx) (t₁, ctx)
  | eval_if_false : ∀ t₁ t₂ ctx,
      Step ((.if_then_else .false t₁ t₂), ctx) (t₂, ctx)
  | eval_if : ∀ t₁ t₁' t₂ t₃ ctx ctx',
      Step (t₁, ctx) (t₁', ctx') →
      Step ((.if_then_else t₁ t₂ t₃), ctx) ((.if_then_else t₁' t₂ t₃), ctx')
  -- `st` is a "store context" which maps pointers to their underlying values.
  -- We're going to do something similar
  -- Would our typechecker need
  | eval_let_in_rhs : ∀ x t₁ t₁' T t₂ ctx ctx',
    Step (t₁, ctx) (t₁', ctx') →
    Step ((.let_in x T t₁ t₂), ctx) ((.let_in x T t₁' t₂), ctx')
  | eval_let_in_body : ∀ x T v₁ t₂ ctx,
    Value v₁ →
    Step ((.let_in x T v₁ t₂), ctx) ((subst x v₁ t₂), ctx) -- FIXME: Add to place context.
  | eval_box_loc : ∀ v₁ ctx,
    Value v₁ →
    Step (.box v₁, ctx) (.loc ctx.size, ctx.push (some v₁))
  | eval_box : ∀ t₁ t₁' ctx ctx',
    Step (t₁, ctx) (t₁', ctx') → 
    Step (.box t₁, ctx) (.box t₁', ctx')
    /-
  | eval_ref : ∀ t₁ t₁' ctx ctx',
    sorry
    -/

-- Lifted from smallstep chapter
-- This is transitive closure with self-loops :)
inductive Multi {α : Type} (R : α → α → Prop) : α → α → Prop where
  | multi_refl : ∀ (a : α), Multi R a a
  | multi_step : ∀ (a b c : α),
                  R a b →
                  Multi R b c →
                  Multi R a c


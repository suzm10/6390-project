-- Simple translation of STLC code from PLF


-- TODO: First pass at modeling a lifetime
-- In a lambda calculus numerical program points might not make much sense
structure Lifetime where
  start : Nat
  finish : Nat
  sound : start ≤ finish
  deriving Repr

inductive Ty : Type where
  | unit : Ty
  | bool : Ty
  | nat : Ty
  | string : Ty -- NOTE: Introducing this as a concrete example of a type that is not trivially copyable.
  | arrow : Ty → Ty → Ty
  | ref : Lifetime → Ty → Ty -- NOTE: First pass, will probably delete once I read RustBelt or Oxide more closely.
  | ref_mut : Lifetime → Ty → Ty
  deriving Repr

inductive Term : Type where
  | var : String → Term
  | abs : String → Ty → Term → Term
  | app : Term → Term → Term
  | true : Term
  | false : Term
  | nat_const : Nat → Term
  | string_const : String → Term
  | if_then_else : Term → Term → Term → Term
  -- TODO: Define constructors for `ref`
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

def owned : Ty → Prop
  | Ty.ref _ _ => False
  | Ty.ref_mut _ _ => False
  | _ => True

-- substitute s for x in t as in [x := s]t
def subst (x : String) (s : Term) (t : Term) : Term :=
  match t with
  | Term.var y =>
      if x = y then s else Term.var y
  | Term.app t₁ t₂ =>
      Term.app (subst x s t₁) (subst x s t₂)
  -- either (y:T, [y:=s] t_1), y is bound so can't substitute
  -- or y is not bound (y:T, [x:=s] t_1)
  | Term.abs y T t₁ => Term.abs y T (if x = y then t₁ else (subst x s t₁))
  | Term.if_then_else t₁ t₂ t₃ =>
      Term.if_then_else (subst x s t₁) (subst x s t₂) (subst x s t₃)
  | Term.true =>  Term.true
  | Term.false => Term.false
  | Term.string_const s => Term.string_const s
  | Term.nat_const n => Term.nat_const n

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
  | eval_if_true : ∀ t₁ t₂,
      Step (Term.if_then_else Term.true t₁ t₂) t₁
  | eval_if_false : ∀ t₁ t₂,
      Step (Term.if_then_else Term.false t₁ t₂) t₂
  | eval_if : ∀ t₁ t₁' t₂ t₃,
      Step t₁ t₁' →
      Step (Term.if_then_else t₁ t₂ t₃) (Term.if_then_else t₁' t₂ t₃)

partial def eval (t : Term) : Term :=
  match t with
  | Term.true => Term.true
  | Term.false => Term.false
  | Term.var x => Term.var x
  | Term.nat_const n => Term.nat_const n
  | Term.string_const s => Term.string_const s
  | Term.abs x T t => Term.abs x T t -- I don't know
  -- | Term.app t₁ t₂ => sorry
  | Term.app t₁ t₂ =>
    match eval t₁ with
    | Term.abs x T₁' t₁' =>
        let v₂ := eval t₂
        eval (subst x v₂ t₁')
    | t₁' =>
        Term.app t₁' (eval t₂)
  | Term.if_then_else t₁ t₂ t₃ =>
    match eval t₁ with
    | Term.true => eval t₂
    | Term.false => eval t₃
    | t' => Term.if_then_else t' t₂ t₃

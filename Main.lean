import RefinementBorrows

-- (λx : bool. λy : bool → string. (y x))
def test_term :=
  Term.abs "x" Ty.bool (Term.abs "y" (Ty.arrow Ty.bool Ty.string) (Term.app (Term.var "y") (Term.var "x")))

def test_if_then_else :=
  Term.if_then_else Term.true (Term.nat_const 1) (Term.nat_const 0)

def test_if_then_else2 :=
  Term.if_then_else Term.false (Term.nat_const 1) (Term.nat_const 0)

def test_subst :=
  subst "x" (Term.nat_const 42) (Term.abs "y" Ty.bool (Term.var "x"))

def test_app :=
  Term.app (Term.abs "x" Ty.bool (Term.var "x")) (Term.nat_const 42)

def main : IO Unit := do
  IO.println "Hello, Sailor!"
  IO.println (repr (eval test_term))
  IO.println (repr (eval test_if_then_else))
  IO.println (repr (eval test_if_then_else2))
  IO.println (repr (eval test_subst))
  IO.println (repr (eval test_app))

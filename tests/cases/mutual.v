Inductive expr : Type :=
| econst : nat -> expr
| eadd : expr -> expr -> expr
with stmt : Type :=
| sassign : expr -> stmt.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | econst _ => 1
  | eadd a b => expr_size a + expr_size b
  end.

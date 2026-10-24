From Stdlib Require Import List Arith.
Import ListNotations.

Inductive expr : Type :=
| Const : nat -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr.

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Add a b => eval a + eval b
  | Mul a b => eval a * eval b
  end.

Fixpoint optimize (e : expr) : expr :=
  match e with
  | Const n => Const n
  | Add a b =>
      match optimize a, optimize b with
      | Const x, Const y => Const (x + y)
      | a', b' => Add a' b'
      end
  | Mul a b =>
      match optimize a, optimize b with
      | Const x, Const y => Const (x * y)
      | a', b' => Mul a' b'
      end
  end.

Lemma eval_optimize : forall e, eval (optimize e) = eval e.
Proof.
  induction e; simpl.
  - reflexivity.
  - destruct (optimize e1) eqn:E1, (optimize e2) eqn:E2; simpl in *;
      rewrite IHe1, IHe2; reflexivity.
  - destruct (optimize e1) eqn:E1, (optimize e2) eqn:E2; simpl in *;
      rewrite IHe1, IHe2; reflexivity.
Qed.

Definition sample : expr := Add (Const 2) (Mul (Const 3) (Const 4)).

Lemma sample_eval : eval sample = 14.
Proof. reflexivity. Qed.

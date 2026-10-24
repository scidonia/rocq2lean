From Stdlib Require Import Arith List Bool.
Import ListNotations.
Require Import Syntax.

Inductive term : Type :=
| Var : nat -> term
| Lit : nat -> term
| Plus : term -> term -> term.

Fixpoint tsubst (x : nat) (v : nat) (t : term) : term :=
  match t with
  | Var y => if Nat.eqb x y then Lit v else Var y
  | Lit n => Lit n
  | Plus a b => Plus (tsubst x v a) (tsubst x v b)
  end.

Fixpoint teval (env : nat -> nat) (t : term) : nat :=
  match t with
  | Var y => env y
  | Lit n => n
  | Plus a b => teval env a + teval env b
  end.

Lemma teval_tsubst :
  forall t env x, teval env (tsubst x (env x) t) = teval env t.
Proof.
  induction t; simpl; intros.
  - destruct (Nat.eqb x n) eqn:E.
    + apply Nat.eqb_eq in E; subst; reflexivity.
    + reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

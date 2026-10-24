From Stdlib Require Import Arith List.
Import ListNotations.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Fixpoint vto_list {A} {n} (v : vec A n) : list A :=
  match v with
  | @vnil _ => []
  | @vcons _ x n' xs => x :: vto_list xs
  end.

Lemma vto_list_length : forall A n (v : vec A n), length (vto_list v) = n.
Proof.
  intros A n v; induction v; simpl.
  - reflexivity.
  - rewrite IHv; reflexivity.
Qed.

Lemma vcons_inj : forall A n (x y : A) (v w : vec A n),
  @vcons A x n v = @vcons A y n w -> x = y.
Proof. intros; inversion H; reflexivity. Qed.

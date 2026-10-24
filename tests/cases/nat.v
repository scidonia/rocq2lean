Require Import Coq.Init.Nat.

Fixpoint plus_n_Sm (n m : nat) : S (n + m) = n + S m :=
  match n with
  | 0 => eq_refl
  | S k => f_equal S (plus_n_Sm k m)
  end.

Lemma add_0_l : forall n : nat, 0 + n = n.
Proof. intro n. reflexivity. Qed.

Definition let_test (n : nat) : nat := let m := n + n in m + m.

Lemma add_0_r : forall n : nat, n + 0 = n.
Proof. induction n. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

Lemma two_inductions : forall n m : nat, n + m = n + m.
Proof. intros n m. induction n; induction m; reflexivity. Qed.

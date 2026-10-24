Inductive nat2 : Type :=
| O2 : nat2
| S2 : nat2 -> nat2.

Definition pred2 (n : nat2) : nat2 :=
  match n with
  | O2 => O2
  | S2 k => k
  end.

Fixpoint plus2 (n m : nat2) : nat2 :=
  match n with
  | O2 => m
  | S2 k => S2 (plus2 k m)
  end.

Theorem plus2_O_l : forall n : nat2, plus2 O2 n = n.
Proof.
  intro n.
  reflexivity.
Qed.

Lemma plus2_O_r : forall n : nat2, plus2 n O2 = n.
Proof. induction n. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

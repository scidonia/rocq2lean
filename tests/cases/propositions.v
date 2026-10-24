Inductive is_zero : nat -> Prop :=
| iz : is_zero 0.

Definition is_zero_def (n : nat) : Prop := n = 0.

Definition a_set : Set := nat.

Lemma iz0 : is_zero 0.
Proof. constructor. Qed.

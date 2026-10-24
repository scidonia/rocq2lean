Lemma and_comm_test : forall A B : Prop, A /\ B -> B /\ A.
Proof. intros A B H. destruct H as [HA HB]. split; assumption. Qed.

Lemma or_comm_test : forall A B : Prop, A \/ B -> B \/ A.
Proof. intros A B H. destruct H as [HA | HB]. - right; assumption. - left; assumption. Qed.

Lemma ex_test : (exists n : nat, n = 0) -> exists m : nat, m = 0.
Proof. intros [n H]. exists n. exact H. Qed.

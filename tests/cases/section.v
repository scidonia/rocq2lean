Section Functions.

Variable A : Type.
Variable f : A -> A.

Definition twice (x : A) : A := f (f x).

Lemma twice_eq : forall x : A, twice x = f (f x).
Proof. reflexivity. Qed.

End Functions.

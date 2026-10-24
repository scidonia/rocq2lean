Record point := mkPoint { px : nat; py : nat }.

Definition origin : point := mkPoint 0 0.

Definition shift (p : point) (d : nat) : point :=
  mkPoint (px p + d) (py p + d).

Lemma shift_px : forall (p : point) (d : nat), px (shift p d) = px p + d.
Proof. intros p d. reflexivity. Qed.

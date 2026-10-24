From Stdlib Require Import Arith List Bool Lia.
Import ListNotations.
Require Import Syntax.

Record limits : Type := {
  max_depth : nat;
  max_size : nat
}.

Definition default_limits : limits := {| max_depth := 10; max_size := 100 |}.

Module Type Bound.
  Parameter cap : nat.
End Bound.

Module Clamp (B : Bound).
  Definition clamp (n : nat) : nat := min n B.cap.

  Lemma clamp_le : forall n, clamp n <= B.cap.
  Proof. intros; apply Nat.le_min_r. Qed.

  Lemma clamp_idem : forall n, clamp (clamp n) = clamp n.
  Proof.
    intros n; unfold clamp; rewrite <- Nat.min_assoc.
    replace (Nat.min B.cap B.cap) with B.cap.
    - reflexivity.
    - symmetry; apply Nat.min_l; apply Nat.le_refl.
  Qed.
End Clamp.

Module C3 : Bound.
  Definition cap := 3.
End C3.

Module Clamp3 := Clamp(C3).

Lemma add_bound : forall a b, a <= 10 -> b <= 10 -> a + b <= 20.
Proof. intros; lia. Qed.

Lemma size_bound : forall l : list nat, length l <= max_size default_limits -> length l <= 100.
Proof. intros; simpl in *; lia. Qed.

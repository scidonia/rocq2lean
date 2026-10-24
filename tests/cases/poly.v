Inductive tree (A : Type) : Type :=
| leaf : A -> tree A
| node : tree A -> tree A -> tree A.

Fixpoint size (A : Type) (t : tree A) : nat :=
  match t with
  | leaf _ a => 1
  | node _ l r => size A l + size A r
  end.

Fixpoint map_tree (A B : Type) (f : A -> B) (t : tree A) : tree B :=
  match t with
  | leaf _ a => leaf B (f a)
  | node _ l r => node B (map_tree A B f l) (map_tree A B f r)
  end.

Definition id_poly (A : Type) (x : A) : A := x.

Lemma map_size : forall (A B : Type) (f : A -> B) (t : tree A),
  size B (map_tree A B f t) = size A t.
Proof.
  intros A B f t. induction t as [a | l IHl r IHr]; simpl.
  - reflexivity.
  - rewrite IHl, IHr. reflexivity.
Qed.

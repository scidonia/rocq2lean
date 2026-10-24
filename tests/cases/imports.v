From Stdlib Require Import Lists.List.

Definition empty_list (A : Type) : list A := @nil A.

Parameter P : nat -> Prop.
Axiom p0 : P 0.

Definition list_head (A : Type) (default : A) (l : list A) : A :=
  match l with
  | nil => default
  | cons x _ => x
  end.

From Corelib Require Import Init.Logic.

Definition eq_sym' (A : Type) (x y : A) (e : x = y) : y = x :=
  match e in _ = y' return y' = x with
  | eq_refl => eq_refl
  end.

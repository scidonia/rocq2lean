(* A mutually recursive fixed point is not carried: Lean's `and` form is
   layout-sensitive inside expressions, so the block is marked instead. *)
Fixpoint even (n : nat) : bool :=
  match n with
  | 0 => true
  | S k => odd k
  end
with odd (n : nat) : bool :=
  match n with
  | 0 => false
  | S k => even k
  end.

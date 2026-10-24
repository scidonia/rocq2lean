Set Primitive Projections.

Record pair2 : Type := mkPair2 { fst2 : nat; snd2 : nat }.

Definition first (p : pair2) : nat := fst2 p.

Lemma first_mk : forall a b, first (mkPair2 a b) = a.
Proof. intros a b. reflexivity. Qed.

Record box (A : Type) := mkBox { unbox : A }.

Definition wrap (A : Type) (x : A) : box A := mkBox A x.

Definition unwrap (A : Type) (b : box A) : A := unbox A b.

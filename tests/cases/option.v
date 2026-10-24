Definition opt_map (A B : Type) (f : A -> B) (o : option A) : option B :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Inductive option_rel (A B : Type) (R : A -> B -> Prop) :
  option A -> option B -> Prop :=
| option_rel_none : option_rel A B R None None
| option_rel_some : forall x y, R x y -> option_rel A B R (Some x) (Some y).

Lemma opt_map_id : forall (A : Type) (o : option A), opt_map A A (fun x => x) o = o.
Proof. intros A o. destruct o; reflexivity. Qed.

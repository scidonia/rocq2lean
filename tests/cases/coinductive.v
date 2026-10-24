(* Lean has no coinductive types: the declaration must be marked, not guessed. *)
CoInductive stream : Type := scons : nat -> stream -> stream.

Variable t : Type.

Definition id_func (x : t) : t := x.

Theorem identity : forall x : t, id_func x = x.
Proof.
  (* Notice how "t" never appears in the context.
  It's a bit weird. *)
  intros x.
  unfold id_func.
  reflexivity.
Qed.
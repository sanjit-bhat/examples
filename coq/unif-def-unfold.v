Module one.
Section proof.
Parameter f : nat -> Prop.
Hypothesis f_unit : f 0.
Definition g (t : nat) := f t.

(* Set Debug "tactic-unification". *)
Goal (g 0).
  apply f_unit.
Qed.
(*
[tactic-unification] Starting unification: f 0 ~= g 0

[tactic-unification] Leaving unification with success
 *)
End proof.
End one.

Module two.
Section proof.
Parameter f : nat -> Prop.
Hypothesis f_unit : f 0 = True.
Definition g (t : nat) := f t.

Goal (g 0 = True).
  Fail rewrite f_unit.
Abort.
(*
[tactic-unification] Starting unification: f 0 ~= g 0

[tactic-unification] Leaving unification with failure
 *)
End proof.
End two.

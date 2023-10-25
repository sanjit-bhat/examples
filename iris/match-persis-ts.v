(* Track at https://gitlab.mpi-sws.org/iris/iris/-/issues/479. *)

From iris.heap_lang Require Import proofmode notation.

Section proof.
Context `{!heapGS Σ}.

Hint Extern 100 (Persistent (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition baz (b: bool) : iProp Σ :=
  if b then True%I else False%I.
Definition bar : iProp Σ :=
  ∃ l : list nat, match l with [] => True | _ => False end.
Definition foo1 : iProp Σ :=
  ∃ b : bool, if b then True else False.
Definition foo2 : iProp Σ :=
  ∀ b : bool, if b then True else False.
Definition foo3 : iProp Σ :=
  ∀ b : bool, if b then True else False.
Opaque foo3.

(* Set Typeclasses Debug. *)
(* Print Instances Persistent. *)

(*
Doesn't trigger anything because it's not unfolding baz.
 *)
Goal ∀ b, Persistent (baz b). intros. Fail apply _. Abort.

Goal Persistent bar. apply _. Qed.

(*
bi.exist_persistent
First starts with forall x, Persistent ite x?
No match for this.
Then it looks for Persistent ite x (inner quantification).
This transformation probably comes from the rule that lets
us commute forall and persistent.
After this, it finds our hint.
Destructs and proves the branches.
 *)
Goal Persistent foo1. apply _. Qed.

(*
Tries bi.forall_persistent.
No match for (BiPersistentlyForall PROP).
But once I switched from (PROP : bi) to (iProp Σ), worked.

bi.forall_persistent :
∀ {PROP : bi},
  BiPersistentlyForall PROP
  → ∀ {A : Type} (Ψ : A → PROP),
      (∀ x : A, Persistent (Ψ x)) → Persistent (∀ x : A, Ψ x)
bi.exist_persistent :
∀ {PROP : bi} {A : Type} (Ψ : A → PROP),
  (∀ x : A, Persistent (Ψ x)) → Persistent (∃ x : A, Ψ x)
 *)
Goal Persistent foo2. apply _. Qed.

(*
TC search doesn't unfold opaque defs.
 *)
Goal Persistent foo3. Fail apply _. Abort.

(*
Another note:
`Hint Rewrite lemma` will cause additional rewriting and unification.
Unification slows things down and also does somewhat silly things like
unfolding definitions.
 *)

End proof.

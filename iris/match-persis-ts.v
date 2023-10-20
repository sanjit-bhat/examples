(* Track at https://gitlab.mpi-sws.org/iris/iris/-/issues/479. *)

From iris.heap_lang Require Import proofmode notation.

Section proof.
Context `{!heapGS Σ}.

Hint Extern 100 (Persistent (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Definition baz (b: bool) : iProp Σ :=
  if b then True%I else False%I.
Definition foo : iProp Σ :=
  ∃ b : bool, if b then True else False.
Definition foo2 : iProp Σ :=
  ∀ b : bool, if b then True else False.
Definition bar : iProp Σ :=
  ∃ l : list nat, match l with [] => True | _ => False end.

(* Set Typeclasses Debug. *)
(* Print Instances Persistent. *)

Goal ∀ b, Persistent (baz b).  intros. Fail apply _. Abort.
(*
Doesn't trigger anything because it's not unfolding baz.
 *)

Goal Persistent foo2. apply _. Qed.
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

Goal Persistent foo. apply _. Qed.
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

Goal Persistent bar. apply _. Qed.
End proof.

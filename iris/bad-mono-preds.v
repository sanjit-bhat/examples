From iris.heap_lang Require Import proofmode notation.

Section proof.

Context `{!heapGS Σ}.

Definition BadTransf :=
    λ (Φ : (val → iProp Σ)),
        (∀ v, Φ v -∗ False)%I.

Lemma BadTransfMono Φ Ψ:
    (∀ v, Φ v -∗ Ψ v) -∗ BadTransf Φ -∗ BadTransf Ψ.
Proof.
    iIntros "Himpl HΦ".
    unfold BadTransf.
    iIntros (v) "HΨ".
    (* This is not provable.
    Going backwards, you need Φ v0,
    but there's no way to get that.
    You would need (Ψ v0 -∗ Φ v0) to do it. *)
Admitted.

Lemma BadTransfNotMono Φ Ψ:
    (∀ v, Ψ v -∗ Φ v) -∗ BadTransf Φ -∗ BadTransf Ψ.
Proof.
    iIntros "Himpl HΦ".
    unfold BadTransf.
    iIntros (v) "HΨ".
    iApply "HΦ".
    iApply "Himpl".
    iAssumption.
Qed.

End proof.

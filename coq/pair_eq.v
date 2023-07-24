Lemma pair_eq (a b c d : nat):
    (a, b) = (c, d) ->
    a = c /\ b = d.
Proof.
    intros Heq.
    inversion Heq.
    eauto.
Qed.
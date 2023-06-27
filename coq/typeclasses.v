Require Import Unicode.Utf8.
Require Import Lia.

Class Show A : Type :=
{
    show : A -> nat
}.

#[local] Instance showBool : Show bool :=
{
    show := fun b => if b then 1 else 0
}.

Print showBool.
Print Show.
Print show.
Compute (show true).

Class Commut (A : Type) (Op : A -> A -> A) :=
{
    commut : ∀ a b, Op a b = Op b a
}.

#[local] Instance commutNatMul : Commut nat Nat.mul.
Proof.
    constructor.
    lia.
Qed.

Theorem trivial A Op a b:
    Commut A Op ->
    Op a b = Op b a.
Proof.
    intros [Hc].
    apply Hc.
Qed.

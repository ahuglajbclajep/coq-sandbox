(* SumOfNatを解いてもらったもの *)

Require Import Arith.


Fixpoint sum (n: nat) {struct n}: nat :=
  match n with
  | O   => O
  | S p => S p + sum p
  end.


Lemma sum_Sn: forall n, sum (S n) = S n + sum n.
Proof.
  simpl; reflexivity.
Qed.

Lemma succ_add: forall n, S n = n + 1.
Proof.
Admitted.

Lemma add_diag: forall n, n + n = 2 * n.
Proof.
Admitted.

Goal forall n m: nat, m = 2 * sum n -> m = n * (n + 1).
Proof.
  induction n.
  - intros; apply H.
  - rewrite sum_Sn.
    intros.
    (* ここまでは分かった *)
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_succ_l.
    rewrite Nat.mul_1_r.
    rewrite <- Nat.add_assoc.
    rewrite add_diag.
    rewrite Nat.add_comm.
    rewrite Nat.mul_add_distr_l in H.
    rewrite (IHn (2 * sum n)) in H.
    rewrite <- succ_add in H.
    apply H.
    reflexivity.
Qed.
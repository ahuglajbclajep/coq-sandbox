(* http://d.hatena.ne.jp/hzkr/20100919 *)

Require Import Arith.


Fixpoint sum (n: nat) :=
  match n with
  | O => 0
  | S m => n + sum m
  end.


Goal forall n: nat, 2 * sum n = n * (n + 1).
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    ring_simplify.
    rewrite IHn.
    ring.
Qed.


(* 別解 *)
Goal forall n: nat, 2 * sum n = n * (n + 1).
Proof.
  induction n.
  - trivial.
  - unfold sum; fold sum.
    rewrite Nat.mul_add_distr_l.
    rewrite IHn.
    ring.
Qed.


Goal forall (n m: nat), m = 2 * sum n -> m = n * (n + 1).
Proof.
  induction n.
  - intros.
    rewrite H.
    reflexivity.
  - intros.
    unfold sum in H; fold sum in H.


Goal forall (m n: nat), m = 2 * sum n -> m = n * (n + 1).
Proof.
  intros m n.
  generalize m.
  induction n.
  - intros n H.
    rewrite H.
    reflexivity.
  -

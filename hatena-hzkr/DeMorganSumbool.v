(* http://d.hatena.ne.jp/hzkr/20100914 *)

Goal forall A B: Prop, ({A} + {B} -> False) -> ((A -> False) /\ (B -> False)).
Proof.
  intros.
  split.

  intros.
  apply H.
  left.
  exact H0.

  intros.
  apply H.
  right.
  exact H0.
Qed.


Goal forall A B: Prop, ((A -> False) /\ (B -> False)) -> ({A} + {B} -> False).
Proof.
  intros.
  destruct H.
  destruct H0.

  exact (H a).

  exact (H1 b).
Qed.
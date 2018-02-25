(* http://d.hatena.ne.jp/hzkr/20100914 *)

Goal forall A B: Prop, ~(A \/ B) -> (~A /\ ~B).
Proof.
  unfold not.
  intros.
  apply conj.

  intros.
  apply H.
  apply or_introl.
  exact H0.

  intros.
  apply H.
  apply or_intror.
  exact H0.
Qed.


(* split, left, right で書き直す *)
Goal forall A B: Prop, ~(A \/ B) -> (~A /\ ~B).
Proof.
  unfold not.
  intros.
  split.

  intros.
  apply H.
  left.
  assumption.

  intros.
  apply H.
  right.
  assumption.
Qed.


(* exactで *)
Goal forall A B: Prop, ~(A \/ B) -> (~A /\ ~B).
Proof.
  unfold not.
  intros.
  exact (conj (fun x => H (or_introl x)) (fun y => H (or_intror y))).
Qed.


(* ↑の逆 *)
Goal forall A B: Prop, (~A /\ ~B) -> ~(A \/ B).
Proof.
  unfold not.
  intros.
  destruct H.
  destruct H0.

  exact (H H0).

  exact (H1 H0).
Qed.

(* http://d.hatena.ne.jp/hzkr/20100914 *)

(* A, B, Cのうち、2つ以上成り立つなら成り立つ *)
Inductive major (A B C : Prop) : Prop :=
  | ab: A -> B -> major A B C
  | bc: B -> C -> major A B C
  | ca: C -> A -> major A B C.


(* majorが成り立つなら、A, B, C全てが成り立たない時majorも成り立たない *)
Goal forall A B C: Prop, major A B C -> ~major (~A) (~B) (~C).
Proof.
  unfold not.
  intros.
  destruct H.

  destruct H0.
  exact (H0 H).
  exact (H0 H1).
  exact (H2 H).

  destruct H0.
  exact (H2 H).
  exact (H0 H).
  exact (H0 H1).

  destruct H0.
  exact (H0 H1).
  exact (H2 H).
  exact (H2 H1).
Qed.

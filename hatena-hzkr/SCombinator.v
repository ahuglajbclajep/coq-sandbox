(* http://d.hatena.ne.jp/hzkr/20100902 *)

(* ゴールを変形する *)
Goal forall P Q R: Prop, (P -> Q -> R) -> (Q -> P) -> Q -> R.
Proof.
  intros.
  apply H.
  (* Pについて *)
  apply H0.
  apply H1.
  (* Qについて *)
  apply H1.
Qed.


(* ↑をexactで *)
Goal forall P Q R: Prop, (P -> Q -> R) -> (Q -> P) -> Q -> R.
Proof.
  intros.
  exact (H (H0 H1) H1).
Qed.


(* 仮定を増やす *)
Goal forall P Q R: Prop, (P -> Q -> R) -> (Q -> P) -> Q -> R.
Proof.
  intros.
  assert (H2 := H0 H1).
  assert (H3 := H H2 H1).
  exact H3.
Qed.

(* ↑をexactで *)
Goal forall P Q R: Prop, (P -> Q -> R) -> (Q -> P) -> Q -> R.
Proof.
  intros.
  specialize (H0 H1).  (* H0を置き換える*)
  exact (H H0 H1).
Qed.

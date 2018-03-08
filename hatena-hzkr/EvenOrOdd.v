(* http://d.hatena.ne.jp/hzkr/20100919 *)

Require Import Omega.


Goal forall n: nat, exists m: nat, n = 2 * m \/ n = 2 * m + 1.
Proof.
  induction n.
  - exists 0.
    left.
    reflexivity.
  - destruct IHn; destruct H.
    + exists x.
      right.
      omega.
    + exists (x + 1).
      left.
      omega.
Qed.
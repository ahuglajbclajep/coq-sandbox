(* http://d.hatena.ne.jp/hzkr/20100919 *)

Require Import Arith.


Goal forall (x:nat), x <> 0 -> x < x + x.
Proof.
  intros.
  destruct x.
  - (* Oの場合 *)
    unfold not in H.
    contradiction H.
    reflexivity.
  - (* S x の場合 *)
    assert (S x = S x + 0) by apply plus_n_O.
    rewrite H0 at 1.
    apply plus_lt_compat_l.
    apply lt_O_Sn.
Qed.


(* より簡単に *)
Goal forall (x:nat), x <> 0 -> x < x + x.
Proof.
  intros.
  destruct x.
  - contradiction H.
    reflexivity.
  - apply Nat.lt_add_pos_r.
    apply Nat.lt_0_succ.
Qed.

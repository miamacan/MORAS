Require Import Bool.

Notation " ! b " := (negb b) (at level 0).

(* Zadatak 1 *)

(* a *)
Goal forall (x y : bool), (x && !y) || (!x && !y) || (!x && y) = !x || !y.
Proof.
  destruct x, y; simpl; reflexivity.
Qed.

(* b *)
Goal forall (x y z : bool), !(!x && y && z) && !(x && y && !z) && (x && !y && z) = x && !y && z.
Proof.
  destruct x, y, z; simpl; reflexivity.
Qed.
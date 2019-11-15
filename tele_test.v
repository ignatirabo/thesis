From Mtac2 Require Import Base MTele Mtac2.
Import Sorts.S.
Import M.notations.
Import M.M.

Let m := @mTele nat (fun _ => mBase).
Let A : MTele_Sort SProp m := fun x => x = x.
Let a : MTele_val (MTele_C SProp SProp M A) :=
  fun x => ret (eq_refl).

(*
Let a : forall x : nat, M (A x) :=
  fun x => ret (eq_refl).
*)

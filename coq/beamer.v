Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

(* Ejemplo 1 *)
Check le_n_S.
Check le_0_n.

Definition le_S (n : nat) : n <= S n.
Proof.
induction n.
- apply (le_0_n 1).
- apply (le_n_S (n) (S n)). exact IHn.
Qed.


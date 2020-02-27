Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Locate add_comm.

About Nat.add_succ_l.

Definition add_example (n : nat) : n + 0 = 0 + n.
Proof.
rewrite Nat.add_comm. reflexivity.
Qed.

Check le_n_S.

Definition le_S (n : nat) : n <= S n.
Proof.
induction n.
- apply (le_0_n 1).
- apply (le_n_S (n) (S n)). exact IHn.
Qed.

Lemma sub_0_r : forall n, n - 0 = n.
Proof. intro n. case n.

[ | intro n']. reflexivity. Qed. 
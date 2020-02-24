Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef MTeleMatch.
Import Sorts.S.
Import M.notations.
Import M.M.

About t.

Check add.

Definition test_match (n : nat) : M nat :=
mmatch n with
| [? x y] add x y => ret n
| O => ret (S O)
| [? n']S n' => ret (S (S n'))
end.

Eval compute in test_match 1.

Definition map {A} {B} (t : A -> B) : forall (l : list A), M (list B) :=
  mfix1 m (l : list A) : M list B :=
    mmatch l with
    | nil => ret nil
    | [? x xs] x::xs => xs' <- m xs;
                       ret ((t x)::xs')
    end.

Definition nmon : (1 + 1 = 2).
Proof.
reflexivity.
Qed.

Print nmon.

Definition MyException : Exception. exact exception. Qed.

Definition wmon : M (1 + 1 = 2) :=
  raise MyException.

Definition univ (P : Prop): M P :=
  raise MyException.